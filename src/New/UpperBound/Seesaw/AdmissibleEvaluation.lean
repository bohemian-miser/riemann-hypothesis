module

public import New.UpperBound.Seesaw.EdgePairEvaluation

/-!
# Placewise local-to-adelic seesaw gluing and admissible evaluation of edge pairs

This file proves that the finite evaluation of a pair of consecutive edges `Y → Y' → Y''` carries
finite Heisenberg translates of the vacuum to admissible combinations of glued translates
(`New.Seesaw.isAdmissibleEval_finEval`), and verifies the hypotheses for `middleDoubleLift` and
`lastDoubleLift`.

## Placewise local-to-adelic factorization

Rather than constructing global coset representatives of finite-adelic lattices on `𝔸f E` via
global idempotent algebra and quotient groups away from `N`, we factor the finite evaluation
place-by-place along the unitary group homomorphism `Z.ω`:

1. **Direct Weil-operator zero term** (`New.Seesaw.exists_zeroTermFin_finHeisenbergOp_vacElem` in
   `EdgePairEvaluation`): once an integral matrix `B = D.latticeLift` satisfies
   `B = D.splitting.iFin * g + D.splitting.isotropicBasisFin * c` for the unitary element
   `g = (γ * diag κ) ⊗ 1` on `Hom(X' ⊕ Unit, (X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit))`, the finite constant term
   sends any Heisenberg translate `W.finHeisenbergOp y W.vacElem` either to `0` or to a root of
   unity times `C₀ • Z.ω (1, g) (Z.finHeisenbergOp (Bᴴ *ᵥ y) Z.vacElem)`. No projection of `y` to
   vectors vanishing above `N` is needed.

2. **Local-to-adelic split-place neighbour unitary** (`New.Seesaw.neighbourUnitary`):
   - At every place `w ∉ P ∪ P̄` not dividing `N`, `π_w` is a unit and the local component of `γ` is
     the identity matrix `1`.
   - At each split place `w ∈ P` (where `N = π π̄`, `P ∩ P̄ = ∅`, and `U(E_w × E_{w̄}) ≅ GL(E_w)`
     via `New.ofSplitPlaces`), `γ` acts trivially outside the 2-dimensional block `{e, e''}`
     (`lastSource`, `lastTarget`) and on `{e, e''}` by the upper-triangular `2 × 2` matrix
     `1 + (π_w - 1) (E_{e,e} + η_w E_{e,e''})` with inverse
     `1 + (π_w⁻¹ - 1) (E_{e,e} + η_w E_{e,e''})`. Unitarity automatically determines its component
     at `w̄ ∈ P̄` as the conjugate transpose inverse
     `1 + (π̄_{w̄}⁻¹ - 1) (E_{e,e} + η̄_{w̄} E_{e'',e})`.
     The neighbour congruences (`New.Seesaw.IsNeighbourVector`) are verified one place `u` at a
     time (`u ∈ P`, `ū ∈ P`, and `u ∉ P ∪ P̄`).

3. **Factoring `Z.ω (1, g) = Z.ω (1, γ ⊗ 1) ∘ Z.ω (1, diag κ ⊗ 1)`**:
   - **Places away from `N` (`diag κ ⊗ 1`)**: `New.Seesaw.isAdmissibleCombination_weil_vacElem`
     expands `Z.ω (1, diag κ ⊗ 1) (Z.finHeisenbergOp (Bᴴ *ᵥ y) Z.vacElem)` directly as an
     admissible combination of translates `Z.finHeisenbergOp w Z.vacElem`, with the lattice index
     dividing `#(PairIndex X X'' × (X' ⊕ Unit) → Ô E ⧸ (β))` via reduction modulo `β`.
   - **Places above `N` (`γ ⊗ 1`)**: for `gcd(N, n) = 1`, any such `w` is integral at `P ∪ P̄`, so
     `Z.finHeisenbergOp w Z.vacElem` is fixed by the local vacuum projection `Z.projOn S` for
     `S = star ⁻¹' P`. Since `γ ⊗ 1` is supported on `S ∪ S̄ = P ∪ P̄`,
     `New.Space.omega_schrodingerOp_of_mem_supportedOn` rewrites `Z.ω (1, γ ⊗ 1)` on `Z.projOn S`
     as `Z.schrodingerOp S` of `x ↦ boxIndicator _ S ((γ ⊗ 1)⁻¹ x)`, which decomposes into the
     sum over residue matrices `r : (X' ⊕ Unit) → P → ZMod N` of Schrödinger translates by
     `neighbourTranslation X X'' r`, producing `doubleLiftGluing` and `gluedTranslate`.

Notions from other files:
* A `Space` is a hermitian space over `E` with a point, an adelic basis that is orthonormal at the
  finite places; the columns of its finite part `V.xFin` span the lattice of `V`. The space `V⁻` is
  `V` with the form negated, and `flipSum V V''` is `V⁻ ⊕ V''`.
* `Grading V N (X ⊕ Unit) m` presents `V` as the orthonormal vectors `X ⊕ Unit` plus a string of `m`
  basis vectors, in which vector `i` pairs only with vector `m - 1 - i`, to `1`, or to `-N` if it is
  the middle vector; `Grading.SpansLattice` says that the point of `V` spans the lattice of the
  basis `gradedLatticeBasis`, in which, for odd `m`, the last vector of `X ⊕ Unit` is glued to the
  middle vector of the string.
* `DoubleLiftData`, called a pair of edges `Y → Y' → Y''`, is the data of two consecutive lifts
  between graded spaces `V`, `V'`, `V''`. It identifies the part of grade zero of `V⁻ ⊕ V''` with
  `(X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit)` plus hyperbolic planes.
* `IsNeighbourVector π δ c x` lists the congruences that glue the last entries of a vector `x`
  indexed by `PairIndex X X'' = (X ⊕ Unit) ⊕ (X'' ⊕ Unit)` to the coefficient `c`.
* `selfOrConj β` is the allowed denominator: `β` on the first block of indices, `β̄` on the second.
* `IsScalingAtM N β δ κ` says that each factor of `κ` is `1` or `δ`, that `δ` has norm one and is
  `1` above `N`, that `β` is a unit above `N`, and that the denominators of `κ` are bounded by `β`
  and `β̄`.

## Relation to the literature

See `New.UpperBound.Seesaw.SeesawIdentity` for related work.
-/

@[expose] public section

noncomputable section

namespace New.Seesaw

/-! ## Denominators, indices, and gluing conditions -/

section Denominators

open NumberField Matrix Valued

variable {E n n₀ : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] {q : ℕ}

/-- The denominators allowed on `X⁻ ⊕ X''`: the integral adele `β` on the first block of indices
and its conjugate on the second. -/
def selfOrConj {ι κ : Type*} (β : Ô E) (j : ι ⊕ κ) : 𝔸f E :=
  if j.isLeft then (β : 𝔸f E) else star (β : 𝔸f E)

omit [IsCMField E] in
/-- A vector `x` lies in `weightedTranslations q d` if and only if, for each index `i` and each
finite place `w` not dividing `q`, the absolute values `v` at `w` of `d i` and `x i` have product at
most one. -/
lemma mem_weightedTranslations {ι : Type*} {d x : ι → 𝔸f E} :
    x ∈ weightedTranslations q d ↔
      ∀ (i : ι) (w : FinPlace E), ↑q ∉ w.asIdeal → v (d i w) * v (x i w) ≤ 1 := by
  simp [weightedTranslations]

/-- The group `weightedTranslations q d` consists of the vectors `y` with denominators `d` away from
`q`: for every index `i` and every place `w` not dividing `q` one has `v (d i w) * v (y i w) ≤ 1`.
The adjoint of an integral matrix `M` maps this group to the one for `d'`, provided that `M i j`
vanishes at the conjugate place `star w` whenever `d i` and `d' j` have different valuations at
`w`. -/
lemma conjTranspose_mulVec_mem_weightedTranslations {M : Matrix n n₀ (𝔸f E)}
    (hM_int : IsIntMatrix (Ô E) M) {d y : n → 𝔸f E} {d' : n₀ → 𝔸f E}
    (hy : y ∈ weightedTranslations q d) (hM_zero : ∀ (i : n) (j : n₀) (w : FinPlace E),
      v (d i w) ≠ v (d' j w) → M i j (star w) = 0) :
    Mᴴ *ᵥ y ∈ weightedTranslations q d' := by
  -- `Mᴴ y` is the sum over the rows `i` of the conjugate of row `i` times `y i`.
  have h_rows : Mᴴ *ᵥ y = ∑ i, fun j ↦ star (M i j) * y i :=
    funext fun j ↦ by simp [mulVec, dotProduct]
  rw [h_rows]
  refine sum_mem fun i _ ↦ mem_weightedTranslations.2 fun j w hw ↦ ?_
  by_cases h_val : v (d i w) = v (d' j w)
  · calc v (d' j w) * v ((star (M i j) * y i) w)
        = v (M i j (star w)) * (v (d i w) * v (y i w)) := by simp [h_val, mul_left_comm]
      _ ≤ 1 :=
        mul_le_one' (mem_Ô.1 (hM_int i j) (star w)) (mem_weightedTranslations.1 hy i w hw)
  · simp [hM_zero i j w h_val]

/-- If `x` lies in `weightedTranslations q d`, then `i ↦ c * star (x (f i))` lies in
`weightedTranslations q` for `i ↦ star (d (f i))`. Here `c` is integral (`hc`) and `f` is any change
of indices. -/
lemma star_mem_weightedTranslations {ι X : Type*} {c : 𝔸f E} (hc : c ∈ Ô E) {d x : ι → 𝔸f E}
    (hx : x ∈ weightedTranslations q d) (f : X → ι) :
    (fun i : X ↦ c * star (x (f i))) ∈ weightedTranslations q fun i : X ↦ star (d (f i)) := by
  refine mem_weightedTranslations.2 fun i w hw ↦ ?_
  calc v (star (d (f i)) w) * v ((c * star (x (f i))) w)
      = v (c w) * v ((d (f i) * x (f i)) (star w)) := by simp [mul_left_comm]
    _ ≤ 1 := mul_le_one' (mem_Ô.1 hc w) (hx (f i) (star w) (by simpa using hw))

end Denominators

/-- The basis indices of the sum `X⁻ ⊕ X''` of two definite spaces: those of the first space are
`X ⊕ Unit` and those of the second `X'' ⊕ Unit`, `Unit` indexing a last basis vector. -/
abbrev PairIndex (X X'' : Type) : Type := (X ⊕ Unit) ⊕ X'' ⊕ Unit

/-- The index of the last basis vector `e` of the first space. -/
abbrev PairIndex.lastSource {X X'' : Type} : PairIndex X X'' := Sum.inl (Sum.inr ())

/-- The index of the last basis vector `e''` of the second space. -/
abbrev PairIndex.lastTarget {X X'' : Type} : PairIndex X X'' := Sum.inr (Sum.inr ())

open PairIndex

section PlacewiseNeighbour

open Matrix Space WeilData Kronecker Exchange Finset Weil Valued stdLattice Gf NumberField
  TensorProduct

variable {E X X' X'' : Type} [Field E] [CMType E] [WeilData E]

/-- The gluing conditions on a vector `x` of `X⁻ ⊕ X''` and an adele `c`, which in the application
is the coefficient of an isotropic vector: `x` is integral except at `e` and `e''`, where it has
denominator at most `π̄`, and its entries there, divided by `π`, are congruent to `c` and `η̄ c`. -/
structure IsNeighbourVector (π : (𝔸f E)ˣ) (δ c : 𝔸f E) (x : PairIndex X X'' → 𝔸f E) : Prop where
  /-- The coefficient `c` is unchanged by `δ`. -/
  mul_coeff : δ * c = c
  /-- The entries other than those at `e` and `e''` are integral. -/
  mem_of_ne (i : PairIndex X X'') (h_source : i ≠ lastSource) (h_target : i ≠ lastTarget) :
    x i ∈ Ô E
  /-- All entries have denominator at most `π̄`. -/
  star_mul_mem (i : PairIndex X X'') : star (π : 𝔸f E) * x i ∈ Ô E
  /-- The entry at `e`, divided by `π`, differs from `c` by an integral adele. -/
  sub_source_mem : c - ↑π⁻¹ * x lastSource ∈ Ô E
  /-- The entry at `e''`, divided by `π`, differs from `η̄ c` by an integral adele, where `η` is the
  unit `normNegOne` of norm `-1`. -/
  sub_target_mem : star (normNegOne (E := E) : 𝔸f E) * c - ↑π⁻¹ * x lastTarget ∈ Ô E

/-- The factors `κ` by which the rows of the standard lattice are scaled at the places dividing
`β` and `β̄`: each is `1` or a fixed adele `δ` of norm one, and nothing happens above `N`. In the
application `β β̄` is the auxiliary level `M` and `δ` generates the ideal `(β / β̄)`. -/
structure IsScalingAtM (N : ℕ) (β : Ô E) (δ : 𝔸f E) (κ : PairIndex X X'' → 𝔸f E) : Prop where
  /-- `δ` has norm one. -/
  mul_star_self_eq_one : δ * star δ = 1
  /-- `δ` is `1` above `N`. -/
  apply_eq_one (w : FinPlace E) (hw : ↑N ∈ w.asIdeal) : δ w = 1
  /-- `β` is a unit above `N`. -/
  v_eq_one (w : FinPlace E) (hw : ↑N ∈ w.asIdeal) : v ((β : 𝔸f E) w) = 1
  /-- Each factor is `1` or `δ`. -/
  eq_one_or_eq (b : PairIndex X X'') : κ b = 1 ∨ κ b = δ
  /-- Each factor has denominator at most `β̄`. -/
  star_mul_mem (b : PairIndex X X'') : star (β : 𝔸f E) * κ b ∈ Ô E
  /-- The factors on `X⁻` have denominator at most `β`, those on `X''` at most `β̄`. -/
  selfOrConj_mul_mem (b : PairIndex X X'') : selfOrConj β b * κ b ∈ Ô E

variable (X X'') in
/-- The translation `n y` attached to residues `y` at `P`: the matrix with row `η ȳ / N` at `e`,
row `-ȳ / N` at `e''` and zero elsewhere. It is supported at the places conjugate to `P`. -/
def neighbourTranslation {P : Finset (FinPlace E)} {N : ℕ} (y : X' → P → ZMod N)
    (i : PairIndex X X'' × X') : 𝔸f E :=
  Sum.elim (0 ⊕ᵥ fun _ ↦ (normNegOne (E := E) : 𝔸f E) * star (residueOverN (y i.2)))
    (0 ⊕ᵥ fun _ ↦ -star (residueOverN (y i.2))) i.1

section BasicRelations

variable {N : ℕ} {P : Finset (FinPlace E)} {π : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E}
  {κ : PairIndex X X'' → 𝔸f E}

omit [WeilData E] in
lemma IsSplitSquarefree.isConjDisjoint (hπ : IsSplitSquarefree P (N : E) π) :
    Set.IsConjDisjoint (P : Set (FinPlace E)) :=
  Set.disjoint_left.2 hπ.star_notMem

omit [WeilData E] in
lemma IsSplitSquarefree.natCast_eq_mul_star (hπ : IsSplitSquarefree P (N : E) π) :
    (N : 𝔸f E) = π * star (π : 𝔸f E) := by
  simpa using hπ.algebraMap_eq_mul_star

omit [WeilData E] in
lemma IsSplitSquarefree.mem_integralAdeles (hπ : IsSplitSquarefree P (N : E) π) :
    (π : 𝔸f E) ∈ Ô E := by
  refine mem_Ô.2 fun w ↦ ?_
  rw [hπ.v_apply]
  split_ifs
  exacts [(WithZero.exp_le_exp.2 (by simp)).trans_eq WithZero.exp_zero, le_rfl]

omit [WeilData E] in
lemma IsSplitSquarefree.star_mem_integralAdeles (hπ : IsSplitSquarefree P (N : E) π) :
    star (π : 𝔸f E) ∈ Ô E :=
  star_mem_Ô hπ.mem_integralAdeles

omit [WeilData E] in
/-- If `π` is a uniformiser on `P` and a unit elsewhere, then `π⁻¹` is integral off `P`. -/
lemma IsSplitSquarefree.one_sub_idem_mul_inv_mem (hπ : IsSplitSquarefree P (N : E) π) :
    (1 - idem P) * (↑π⁻¹ : 𝔸f E) ∈ Ô E := by
  rw [← idem_compl, idem_mul_mem_Ô]
  intro w (hw : w ∉ P)
  simp [idele_inv_apply_and_ne_zero, hπ.v_apply, hw]

omit [WeilData E] in
lemma star_mul_star_inv (π : (𝔸f E)ˣ) : star (π : 𝔸f E) * star (↑π⁻¹ : 𝔸f E) = 1 := by
  rw [← star_mul', π.mul_inv, star_one]

lemma normNegOne_mem : (normNegOne (E := E) : 𝔸f E) ∈ Ô E :=
  SetLike.coe_mem _

omit [WeilData E] in
/-- Every scaling factor has norm one. -/
lemma IsScalingAtM.apply_mul_star_eq_one (hκ : IsScalingAtM N β δ κ) (i : PairIndex X X'') :
    κ i * star (κ i) = 1 := by
  rcases hκ.eq_one_or_eq i with h | h <;> simp [h, hκ.mul_star_self_eq_one]

omit [WeilData E] in
/-- If the scaling data `β`, `δ`, `κ` are away from `N` (`hκ`), then `β` is a unit above `N`, hence
so are `β̄` and every denominator `selfOrConj β b` (`β` on the first block, `β̄` on the second). -/
lemma v_selfOrConj_eq_one (hκ : IsScalingAtM N β δ κ) {ι ι' : Type} (b : ι ⊕ ι') {w : FinPlace E}
    (hw : ↑N ∈ w.asIdeal) : v (selfOrConj β b w) = 1 := by
  rw [selfOrConj]
  split_ifs
  exacts [hκ.v_eq_one w hw, (v_star_apply ..).trans (hκ.v_eq_one (star w) (by simpa using hw))]

omit [WeilData E] in
/-- The conjugate of `residueOverN y` (the adele `y w / N` at `w ∈ P`, `0` elsewhere) is unchanged
by multiplication with the conjugate of `idem P`, so it is supported at the places conjugate to
`P`. -/
lemma star_idem_mul_star_residueOverN [Fact N.Prime] (y : P → ZMod N) :
    star (idem P) * star (residueOverN y) = star (residueOverN y) := by
  rw [← star_mul', idem_mul_residueOverN]

/-- The translation `n y = neighbourTranslation X X'' y` is supported at the places conjugate to
`P`: multiplication by `star (idem P)`, the idempotent `j̄` of these places, fixes it. -/
lemma star_idem_smul_neighbourTranslation [Fact N.Prime] (y : X' → P → ZMod N) :
    star (idem P : 𝔸f E) • neighbourTranslation X X'' y = neighbourTranslation X X'' y := by
  ext1 ⟨i, a⟩
  rcases i with (i | i) | (i | i) <;>
    simp [neighbourTranslation, mul_left_comm _ (normNegOne (E := E) : 𝔸f E),
      star_idem_mul_star_residueOverN (y a)]

/-- Let `N = π π̄` with no place of `P` conjugate to one in `P` (`hπ`). A vector `x` fixed by
multiplication by the conjugate of `idem P` (the adele with component `1` on `P` and `0` elsewhere)
is supported at the places conjugate to `P`, so `x* x = 0`. Hence `semichar x`, an additive
character of a multiple of `x* x`, is `1`. -/
lemma semichar_eq_one_of_smul_eq (hπ : IsSplitSquarefree P (N : E) π) {ι : Type} [Fintype ι]
    {x : ι → 𝔸f E} (hx : star (idem P : 𝔸f E) • x = x) : semichar x = 1 := by
  apply semichar_eq_one_of_dotProduct_self_eq_zero
  rw [← hx, star_smul, star_star, smul_dotProduct, dotProduct_smul, smul_smul,
    idem_mul_star hπ.isConjDisjoint, zero_smul]

end BasicRelations

/-! ### Local `2 × 2` split-place neighbour operator and `ofSplitPlaces` gluing -/

section LocalSplitBlock

variable [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X'] [Fintype X''] [DecidableEq X'']
  {N : ℕ} {P : Finset (FinPlace E)} {π : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E}
  {κ : PairIndex X X'' → 𝔸f E}

/-- The upper-triangular `2 × 2` gluing idempotent `E_{e,e} + η E_{e,e''}` on `PairIndex X X''`,
supported on the single 2-dimensional block `{e, e''}` (`lastSource`, `lastTarget`). Because
`e ≠ e''`, this matrix satisfies `Q ^ 2 = Q` over any commutative ring, so `1 + (p - 1) • Q` is
invertible with inverse `1 + (p⁻¹ - 1) • Q` for every unit `p`. -/
def localGlueProj {R : Type*} [Zero R] [One R] [DecidableEq (PairIndex X X'')] (η : R) :
    Matrix (PairIndex X X'') (PairIndex X X'') R :=
  of fun i j ↦
    if i = lastSource then if j = lastSource then 1 else if j = lastTarget then η else 0 else 0

omit [Field E] [CMType E] [WeilData E] [Fintype X'] [DecidableEq X'] in
/-- Because `lastTarget ≠ lastSource`, the rank-one matrix `E_{e,e} + η E_{e,e''}` is idempotent. -/
lemma localGlueProj_mul_self {R : Type*} [CommRing R] (η : R) :
    localGlueProj (X := X) (X'' := X'') η * localGlueProj η = localGlueProj η := by
  ext i k
  rw [Matrix.mul_apply, Fintype.sum_eq_single lastSource
    (fun j hj ↦ by simp [localGlueProj, hj])]
  by_cases hi : i = lastSource <;> simp [localGlueProj, hi]

/-- The local invertible matrix `1 + (p - 1) (E_{e,e} + η E_{e,e''})` in `GL (PairIndex X X'') R`
that acts as the identity outside `{e, e''}` and as the upper-triangular `2 × 2` block
`[[p, (p - 1) η], [0, 1]]` on `{e, e''}`. -/
def localNeighbourGL {R : Type*} [CommRing R] (p : Rˣ) (η : R) : GL (PairIndex X X'') R :=
  have h_mul (a b : R) (hab : a * b = 1) :
      (1 + (a - 1) • localGlueProj (X := X) (X'' := X'') η) *
        (1 + (b - 1) • localGlueProj η) = 1 := by
    have h0 : (a - 1) + (b - 1) + (b - 1) * (a - 1) = 0 := by linear_combination hab
    calc (1 + (a - 1) • localGlueProj η) * (1 + (b - 1) • localGlueProj η)
        = 1 + ((a - 1) + (b - 1) + (b - 1) * (a - 1)) • localGlueProj η := by
          simp [add_mul, mul_add, smul_smul, localGlueProj_mul_self, add_smul, add_assoc]
      _ = 1 := by simp [h0]
  ⟨1 + (p.val - 1) • localGlueProj η, 1 + ((p⁻¹).val - 1) • localGlueProj η,
    h_mul _ _ p.val_inv, h_mul _ _ p.inv_val⟩

variable (X X'') in
/-- The finite-adelic neighbour unitary `γ` on `PairIndex X X''`, assembled locally at the split
places `w ∈ P` via `New.ofSplitPlaces`: at `w ∈ P` it is `localNeighbourGL π_w η_w`, at `w̄ ∈ P̄` it
is the conjugate transpose inverse `1 + (π̄_{w̄}⁻¹ - 1) (E_{e,e} + η̄_{w̄} E_{e'',e})`, and at every
place `w ∉ P ∪ P̄` it is the identity matrix `1`. -/
def neighbourUnitary (hπ : IsSplitSquarefree P (N : E) π) : Gf E (PairIndex X X'') :=
  ofSplitPlaces hπ.star_notMem fun w ↦
    localNeighbourGL (Units.map (evalAt w.val).toMonoidHom π)
      (evalAt w.val (normNegOne (E := E) : 𝔸f E))

variable (X X'') (P π) in
/-- The isotropic-plane coefficient paired with each column of `neighbourUnitary`: `N⁻¹` at `P̄` for
column `e`, `-η / π` at `P` for column `e''`, and `0` on all other columns and at all places outside
`P ∪ P̄`. -/
def neighbourCoeff : PairIndex X X'' → 𝔸f E :=
  (0 ⊕ᵥ fun _ ↦ star (idem P) * (↑π⁻¹ : 𝔸f E) * star (↑π⁻¹ : 𝔸f E)) ⊕ᵥ
    (0 ⊕ᵥ fun _ ↦ -idem P * (↑π⁻¹ : 𝔸f E) * (normNegOne (E := E) : 𝔸f E))

/-- At a place `u ∈ P`, the local matrix of `neighbourUnitary` is
`1 + (π_u - 1) • localGlueProj η_u`. -/
lemma evalAt_neighbourUnitary_of_mem (hπ : IsSplitSquarefree P (N : E) π) {u : FinPlace E}
    (hu : u ∈ P) (i j : PairIndex X X'') :
    evalAt u ((neighbourUnitary X X'' hπ : Matrix (PairIndex X X'') (PairIndex X X'') (𝔸f E)) i j) =
      (1 + (evalAt u (π : 𝔸f E) - 1) •
        localGlueProj (evalAt u (normNegOne (E := E) : 𝔸f E))) i j := by
  change ((neighbourUnitary X X'' hπ).atPlace (⟨u, hu⟩ : P).val).val i j = _
  rw [neighbourUnitary, atPlace_ofSplitPlaces]
  rfl

/-- At a place `u` conjugate to `P` (`star u ∈ P`), unitarity identifies the local matrix of
`neighbourUnitary` with the transpose `(1 + (π̄_u⁻¹ - 1) • localGlueProj η̄_u)ᵀ`. -/
lemma evalAt_neighbourUnitary_of_star_mem (hπ : IsSplitSquarefree P (N : E) π) {u : FinPlace E}
    (hu : star u ∈ P) (i j : PairIndex X X'') :
    evalAt u ((neighbourUnitary X X'' hπ : Matrix (PairIndex X X'') (PairIndex X X'') (𝔸f E)) i j) =
      (1 + (evalAt u (star (↑π⁻¹ : 𝔸f E)) - 1) •
        localGlueProj (evalAt u (star (normNegOne (E := E) : 𝔸f E)))) j i := by
  have h_at : (neighbourUnitary X X'' hπ).atPlace (star u) =
      localNeighbourGL (Units.map (evalAt (star u)).toMonoidHom π)
        (evalAt (star u) (normNegOne (E := E) : 𝔸f E)) :=
    atPlace_ofSplitPlaces hπ.star_notMem _ ⟨star u, hu⟩
  change ((neighbourUnitary X X'' hπ).atPlace u).val i j = _
  rw [Gf.atPlace_star (star_star u), h_at]
  have h_pi : (conjLoc (star_star u) ((π : 𝔸f E) (star u)))⁻¹ =
      conjLoc (star_star u) ((↑π⁻¹ : 𝔸f E) (star u)) := by
    rw [← map_inv₀]
    congr 1
    exact inv_eq_of_mul_eq_one_right (congrArg (evalAt (star u)) π.mul_inv)
  simp only [localNeighbourGL, Units.inv_mk, transpose_apply, Matrix.map_apply, Matrix.add_apply,
    Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one,
    Units.coe_map, localGlueProj, of_apply]
  split_ifs <;> simp [h_pi]

/-- Outside `P` and `P̄`, `neighbourUnitary` has local component `1`. -/
lemma evalAt_neighbourUnitary_of_notMem (hπ : IsSplitSquarefree P (N : E) π) {u : FinPlace E}
    (hu : u ∉ P) (hu_star : star u ∉ P) (i j : PairIndex X X'') :
    evalAt u ((neighbourUnitary X X'' hπ : Matrix (PairIndex X X'') (PairIndex X X'') (𝔸f E)) i j) =
      (1 : Matrix (PairIndex X X'') (PairIndex X X'') (LocField u)) i j := by
  change ((neighbourUnitary X X'' hπ).atPlace u).val i j = _
  rw [neighbourUnitary, Gf.mem_supportedOn.1 (ofSplitPlaces_mem_supportedOn _ _) u hu hu_star]
  rfl

omit [Fintype X] [DecidableEq X] [Fintype X''] [DecidableEq X''] in
/-- Outside `P` and `P̄`, `neighbourCoeff` vanishes. -/
lemma neighbourCoeff_apply_of_notMem {u : FinPlace E} (hu : u ∉ P) (hu_star : star u ∉ P)
    (j : PairIndex X X'') : evalAt u (neighbourCoeff X X'' P π j) = 0 := by
  rcases j with (j | j) | (j | j) <;>
    simp [neighbourCoeff, evalAt_apply, star_idem, hu, hu_star]

/-- Placewise verification that each column `j` of `neighbourUnitary`, paired with
`neighbourCoeff X X'' P π j`, satisfies the neighbour congruences `IsNeighbourVector`:
at `u ∈ P` only the `2 × 2` upper-triangular block enters, at `ū ∈ P` only its transpose inverse
enters (and `π_u` is a unit), and at `u ∉ P ∪ P̄` the column is a standard basis vector with `π_u` a
unit. -/
lemma isNeighbourVector_col_neighbourUnitary (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) (j : PairIndex X X'') :
    IsNeighbourVector π δ (neighbourCoeff X X'' P π j)
      ((neighbourUnitary X X'' hπ : Matrix (PairIndex X X'') (PairIndex X X'') (𝔸f E)).col j) := by
  let M : Matrix (PairIndex X X'') (PairIndex X X'') (𝔸f E) := neighbourUnitary X X'' hπ
  let η : 𝔸f E := normNegOne (E := E)
  have h_st : (lastSource : PairIndex X X'') ≠ lastTarget := Sum.inl_ne_inr
  have h_ts : (lastTarget : PairIndex X X'') ≠ lastSource := Sum.inr_ne_inl
  have hη_mem (u : FinPlace E) : v (η u) ≤ 1 := mem_Ô.1 normNegOne_mem u
  have h_star_η_mem (u : FinPlace E) : v (star η u) ≤ 1 := mem_Ô.1 (star_mem_Ô normNegOne_mem) u
  have hπ_mem (u : FinPlace E) : v ((π : 𝔸f E) u) ≤ 1 := mem_Ô.1 hπ.mem_integralAdeles u
  have h_star_π_mem (u : FinPlace E) : v (star (π : 𝔸f E) u) ≤ 1 :=
    mem_Ô.1 hπ.star_mem_integralAdeles u
  have hv_inv_of_notMem {u : FinPlace E} (hu : u ∉ P) : v ((↑π⁻¹ : 𝔸f E) u) = 1 := by
    simp [idele_inv_apply_and_ne_zero, hπ.v_apply, hu]
  have h_one_entry (u : FinPlace E) (a b : PairIndex X X'') :
      v ((1 : Matrix (PairIndex X X'') (PairIndex X X'') (LocField u)) a b) ≤ 1 := by
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  refine
    { mul_coeff := ?_
      mem_of_ne := fun i hi_s hi_t ↦ mem_Ô.2 fun u ↦ ?_
      star_mul_mem := fun i ↦ mem_Ô.2 fun u ↦ ?_
      sub_source_mem := mem_Ô.2 fun u ↦ ?_
      sub_target_mem := mem_Ô.2 fun u ↦ ?_ }
  · -- `neighbourCoeff` is supported on `P ∪ P̄`, where `δ = 1`.
    ext u
    by_cases hu : u ∈ P ∨ star u ∈ P
    · simp [hκ.apply_eq_one u ((hP.natCast_mem_iff u).2 hu)]
    · obtain ⟨huP, huS⟩ := not_or.1 hu
      have h0 : neighbourCoeff X X'' P π j u = 0 := neighbourCoeff_apply_of_notMem huP huS j
      simp [h0]
  · -- For `i ≠ e, e''`, row `i` of `M` is the row of the identity matrix at every place `u`.
    change v (evalAt u (M i j)) ≤ 1
    by_cases hu : u ∈ P
    · rw [evalAt_neighbourUnitary_of_mem hπ hu]
      simpa [localGlueProj, hi_s] using h_one_entry u i j
    · by_cases huS : star u ∈ P
      · rw [evalAt_neighbourUnitary_of_star_mem hπ huS]
        simpa [localGlueProj, hi_s, hi_t] using h_one_entry u j i
      · rw [evalAt_neighbourUnitary_of_notMem hπ hu huS]
        exact h_one_entry u i j
  · -- `π̄ * M i j` is integral at every place `u`.
    change v (star (π : 𝔸f E) u * evalAt u (M i j)) ≤ 1
    by_cases hu : u ∈ P
    · rw [evalAt_neighbourUnitary_of_mem hπ hu]
      have hM_int : v ((1 + (evalAt u (π : 𝔸f E) - 1) • localGlueProj (evalAt u η)) i j) ≤ 1 := by
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, localGlueProj, of_apply]
        refine v.map_add_le (h_one_entry u i j) ?_
        rw [map_mul]
        refine mul_le_one' (v.map_sub_le (hπ_mem u) (by simp)) ?_
        split_ifs <;> simp [evalAt_apply, hη_mem u]
      rw [map_mul]
      exact mul_le_one' (h_star_π_mem u) hM_int
    · by_cases huS : star u ∈ P
      · rw [evalAt_neighbourUnitary_of_star_mem hπ huS]
        have h_cancel : star (π : 𝔸f E) u * (evalAt u (star (↑π⁻¹ : 𝔸f E)) - 1) =
            1 - star (π : 𝔸f E) u := by
          have h1 : star (π : 𝔸f E) u * evalAt u (star (↑π⁻¹ : 𝔸f E)) = 1 :=
            congrArg (evalAt u) (star_mul_star_inv π)
          linear_combination h1
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add, ← mul_assoc, h_cancel,
          localGlueProj, of_apply]
        refine v.map_add_le
          (by rw [map_mul]; exact mul_le_one' (h_star_π_mem u) (h_one_entry u j i)) ?_
        rw [map_mul]
        refine mul_le_one' (v.map_sub_le (by simp) (h_star_π_mem u)) ?_
        split_ifs <;> simp [evalAt_apply]
        exact hη_mem (star u)
      · rw [evalAt_neighbourUnitary_of_notMem hπ hu huS, map_mul]
        exact mul_le_one' (h_star_π_mem u) (h_one_entry u i j)
  · -- Congruence `c - π⁻¹ * M e j ∈ Ô` at row `e = lastSource`, checked place-by-place.
    change v (evalAt u (neighbourCoeff X X'' P π j) -
      (↑π⁻¹ : 𝔸f E) u * evalAt u (M lastSource j)) ≤ 1
    by_cases hu : u ∈ P
    · have huS : star u ∉ P := hπ.star_notMem u hu
      have h_inv : (↑π⁻¹ : 𝔸f E) u * (π : 𝔸f E) u = 1 := congrArg (evalAt u) π.inv_mul
      rw [evalAt_neighbourUnitary_of_mem hπ hu]
      rcases j with (j | ⟨⟩) | (j | ⟨⟩) <;>
        simp [neighbourCoeff, localGlueProj, star_idem, hu, huS, h_st, h_inv]
      refine le_of_eq_of_le (congrArg v (show _ = -η u by linear_combination -(η u) * h_inv)) ?_
      simpa using hη_mem u
    · by_cases huS : star u ∈ P
      · rw [evalAt_neighbourUnitary_of_star_mem hπ huS]
        rcases j with (j | ⟨⟩) | (j | ⟨⟩) <;>
          simp [neighbourCoeff, localGlueProj, star_idem, hu, huS, h_ts]
      · rw [evalAt_neighbourUnitary_of_notMem hπ hu huS, neighbourCoeff_apply_of_notMem hu huS,
          zero_sub, v.map_neg, map_mul, hv_inv_of_notMem hu, one_mul]
        exact h_one_entry u lastSource j
  · -- Congruence `η̄ * c - π⁻¹ * M e'' j ∈ Ô` at row `e'' = lastTarget`, checked place-by-place.
    change v (star η u * evalAt u (neighbourCoeff X X'' P π j) -
      (↑π⁻¹ : 𝔸f E) u * evalAt u (M lastTarget j)) ≤ 1
    by_cases hu : u ∈ P
    · have huS : star u ∉ P := hπ.star_notMem u hu
      rw [evalAt_neighbourUnitary_of_mem hπ hu]
      rcases j with (j | ⟨⟩) | (j | ⟨⟩) <;>
        simp [neighbourCoeff, localGlueProj, star_idem, hu, huS, h_ts]
      have h_norm_u : conjLoc (star_star u) (η (star u)) * η u = -1 := by
        rw [← evalAt_apply (star u), ← evalAt_star_eq_conjLoc (star_star u)]
        exact congrArg (evalAt u) (star_normNegOne_mul_self (E := E))
      exact le_of_eq_of_le
        (congrArg v (show _ = 0 by linear_combination -((↑π⁻¹ : 𝔸f E) u) * h_norm_u)) (by simp)
    · by_cases huS : star u ∈ P
      · rw [evalAt_neighbourUnitary_of_star_mem hπ huS]
        rcases j with (j | ⟨⟩) | (j | ⟨⟩) <;>
          simp [neighbourCoeff, localGlueProj, star_idem, hu, huS, h_st, hv_inv_of_notMem hu]
        refine le_of_eq_of_le (congrArg v (show _ = (↑π⁻¹ : 𝔸f E) u * star η u by
          simp only [← evalAt_apply, evalAt_star_eq_conjLoc (star_star u)]; ring)) ?_
        rw [map_mul, hv_inv_of_notMem hu, one_mul]
        exact h_star_η_mem u
      · rw [evalAt_neighbourUnitary_of_notMem hπ hu huS, neighbourCoeff_apply_of_notMem hu huS,
          mul_zero, zero_sub, v.map_neg, map_mul, hv_inv_of_notMem hu, one_mul]
        exact h_one_entry u lastTarget j

/-- The diagonal matrix of the factors `κ`, each of which has norm one, as a finite point of the
unitary group. -/
def scalingUnitary (hκ : IsScalingAtM N β δ κ) : Gf E (PairIndex X X'') :=
  U.of isUnit_one (diagonal κ) <| by simp [mul_comm (star _), hκ.apply_mul_star_eq_one]

/-- Because `neighbourUnitary` is supported on `P ∪ P̄` and `scalingUnitary` is trivial on `P`, the
two unitary elements commute. -/
lemma commute_neighbourUnitary_scalingUnitary (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) :
    Commute (neighbourUnitary X X'' hπ) (scalingUnitary hκ) := by
  refine Gf.commute_supportedOn_trivialOn (ofSplitPlaces_mem_supportedOn _ _)
    (Gf.mem_trivialOn.2 fun w hw ↦ ?_)
  ext1
  change (diagonal κ).map (evalAt w) = 1
  ext i j
  by_cases hij : i = j
  · subst hij
    have hκw : κ i w = 1 := by
      rcases hκ.eq_one_or_eq i with h | h <;>
        simp [h, hκ.apply_eq_one w ((hP.natCast_mem_iff w).2 (Or.inl hw))]
    simp [evalAt_apply, hκw]
  · simp [hij]

section KroneckerAndBox

variable (X') in
/-- The homomorphism `g ↦ g ⊗ 1`. Its values act on matrices with columns indexed by `X'` by left
multiplication with `g`. -/
def kroneckerOne (ι : Type) [Fintype ι] [DecidableEq ι] : Gf E ι →* Gf E (ι × X') :=
  (U.kroneckerHom (S := (1 : Matrix X' X' (𝔸f E))) (one_mul 1) (by simp)).comp
    (MonoidHom.inr (U (1 : Matrix X' X' (𝔸f E))) (Gf E ι))

omit [WeilData E] in
/-- The matrix of `g ⊗ 1` is the Kronecker product of that of `g` with the identity. -/
lemma coe_kroneckerOne {ι : Type} [Fintype ι] [DecidableEq ι] (g : Gf E ι) :
    (kroneckerOne X' ι g : Matrix (ι × X') (ι × X') (𝔸f E)) =
      (g : Matrix ι ι (𝔸f E)) ⊗ₖ (1 : Matrix X' X' (𝔸f E)) := by
  simp [kroneckerOne]

omit [WeilData E] in
/-- The action of `g ⊗ 1` on a matrix `x` multiplies each column of `x` by `g`. -/
lemma kroneckerOne_smul {ι : Type} [Fintype ι] [DecidableEq ι] (g : Gf E ι) (x : ι × X' → 𝔸f E)
    (i : ι × X') :
    (kroneckerOne X' ι g • x) i = ((g : Matrix ι ι (𝔸f E)) *ᵥ fun l : ι ↦ x (l, i.2)) i.1 := by
  change ((kroneckerOne X' ι g : Matrix (ι × X') (ι × X') (𝔸f E)) *ᵥ x) i = _
  simp [coe_kroneckerOne, mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]

omit [WeilData E] in
/-- The element `scalingUnitary hκ ⊗ 1`, where `scalingUnitary hκ` is the diagonal matrix of the
factors `κ`, multiplies row `i.1` of a matrix `x` by `κ i.1`. -/
lemma kroneckerOne_scalingUnitary_smul (hκ : IsScalingAtM N β δ κ)
    (x : PairIndex X X'' × X' → 𝔸f E) (i : PairIndex X X'' × X') :
    (kroneckerOne X' (PairIndex X X'') (scalingUnitary hκ) • x) i = κ i.1 * x i := by
  rw [kroneckerOne_smul]
  exact mulVec_diagonal κ _ i.1

omit [WeilData E] in
/-- If `g` has local component `1` at `w`, so does `g ⊗ 1`. -/
lemma kroneckerOne_atPlace_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] (g : Gf E ι)
    {w : FinPlace E} (hg : g.atPlace w = 1) : (kroneckerOne X' ι g).atPlace w = 1 := by
  ext1
  change (kroneckerOne X' ι g : Matrix (ι × X') (ι × X') (𝔸f E)).map (evalAt w) = 1
  have hg' : (g : Matrix ι ι (𝔸f E)).map (evalAt w) = 1 := congrArg Units.val hg
  rw [coe_kroneckerOne, map_kronecker, hg', Matrix.map_one _ (map_zero _) (map_one _),
    one_kronecker_one]

variable (X') in
/-- The unitary `(γ κ) ⊗ 1`. It carries the standard lattice of `Hom (X', X⁻ ⊕ X'')` to the lattice
that is the neighbour above `N` and has its rows scaled by `κ` elsewhere. -/
def latticeUnitary (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) :
    Gf E (PairIndex X X'' × X') :=
  kroneckerOne X' (PairIndex X X'') (neighbourUnitary X X'' hπ * scalingUnitary hκ)

/-- At a level prime `N` split as `P` and its conjugate, the matrix of `latticeUnitary` is
`(diagonal κ * γ) ⊗ 1`, where `γ = neighbourUnitary X X'' hπ`. -/
lemma coe_latticeUnitary (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) :
    (latticeUnitary X' hπ hκ : Matrix (PairIndex X X'' × X') (PairIndex X X'' × X') (𝔸f E)) =
      (diagonal κ * (neighbourUnitary X X'' hπ : Matrix _ _ (𝔸f E))) ⊗ₖ
        (1 : Matrix X' X' (𝔸f E)) := by
  rw [latticeUnitary, (commute_neighbourUnitary_scalingUnitary hP hπ hκ).eq, coe_kroneckerOne]
  rfl

/-- Let the prime `N` be split as `P` and its conjugate, let `π` be split squarefree for `N` at `P`,
let `η = normNegOne` have norm `-1` and, for residues `y` modulo `N` at the places of `P`, let
`residueOverN y` be the adele `y / N` at `P` and `0` elsewhere. Multiplication by the conjugate of
`idem P` keeps only the places conjugate to `P`. If `t` is integral there, then `π̄⁻¹ t + η ȳ / N`
is integral there for exactly one family of residues `y`, and otherwise for none. -/
lemma exists_class_star_idem_mul_mem_iff [Fact N.Prime] (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (t : 𝔸f E) :
    ∃ y₀ : P → ZMod N, ∀ y : P → ZMod N,
      star (idem P) * (star (↑π⁻¹ : 𝔸f E) * t +
        (normNegOne (E := E) : 𝔸f E) * star (residueOverN y)) ∈ Ô E ↔
      star (idem P) * t ∈ Ô E ∧ y₀ = y := by
  set η : 𝔸f E := ↑(normNegOne (E := E))
  have hη_norm : star η * η = -1 := star_normNegOne_mul_self
  have hη_mem : η ∈ Ô E := normNegOne_mem
  -- The map `w ↦ η w̄` preserves integrality in both directions.
  have h_twist (w : 𝔸f E) : η * star w ∈ Ô E ↔ w ∈ Ô E := by
    refine ⟨fun h ↦ ?_, fun h ↦ mul_mem hη_mem (star_mem_Ô h)⟩
    have h_inv : η * star (η * star w) = -w := by
      rw [star_mul', star_star, ← mul_assoc, mul_comm η (star η), hη_norm, neg_one_mul]
    simpa only [h_inv, neg_mem_iff] using mul_mem hη_mem (star_mem_Ô h)
  -- It turns the left side into `z - y / N` at `P`.
  set z : 𝔸f E := η * ↑π⁻¹ * star t with hz
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : P → ZMod N, ∀ y : P → ZMod N,
      idem P * (z - residueOverN y) ∈ Ô E ↔ idem P * ((N : 𝔸f E) * z) ∈ Ô E ∧ y₀ = y :=
    hP.exists_sub_residueOverN_mem_iff z
  refine ⟨y₀, fun y ↦ ?_⟩
  have h_sub : η * star (star (idem P) * (star (↑π⁻¹ : 𝔸f E) * t + η * star (residueOverN y))) =
      idem P * (z - residueOverN y) := by
    simp only [hz, star_mul', star_add, star_star]
    grind
  -- `N z = η π̄ t̄`, and `π̄` is a unit at `P`.
  have h_mul : idem P * ((N : 𝔸f E) * z) = star (π : 𝔸f E) * (η * star (star (idem P) * t)) := by
    simp only [hz, hπ.natCast_eq_mul_star, star_mul', star_star]
    grind [π.mul_inv]
  have h_div : η * star (star (idem P) * t) =
      star ((1 - idem P) * (↑π⁻¹ : 𝔸f E)) * (idem P * ((N : 𝔸f E) * z)) := by
    simp only [h_mul, star_sub, star_one, star_mul', star_star]
    grind [idem_mul_star hπ.isConjDisjoint, star_mul_star_inv π]
  rw [← h_twist, h_sub, hy₀, ← h_twist (star (idem (P : Set (FinPlace E))) * t)]
  refine and_congr_left' ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h_div]
    exact mul_mem (star_mem_Ô hπ.one_sub_idem_mul_inv_mem) h
  · rw [h_mul]
    exact mul_mem hπ.star_mem_integralAdeles h

omit [Fintype X'] [DecidableEq X'] in
/-- Placewise evaluation at `P̄`: after multiplication by `star (idem P)`, each column of
`γ x + n y` equals `x` plus `(e + η̄ e'')` times `(π̄⁻¹ x_e + η ȳ / N) - x_e` at `P̄`. -/
lemma star_idem_mul_neighbourUnitary_add_translation [Fact N.Prime]
    (hπ : IsSplitSquarefree P (N : E) π) (x : PairIndex X X'' × X' → 𝔸f E)
    (y : X' → P → ZMod N) (i : PairIndex X X'' × X') :
    star (idem P) * (((neighbourUnitary X X'' hπ : Matrix _ _ (𝔸f E)) *ᵥ
        fun l : PairIndex X X'' ↦ x (l, i.2)) i.1 + neighbourTranslation X X'' y i) =
      star (idem P) * x i +
        (if i.1 = lastSource then 1
          else if i.1 = lastTarget then star (normNegOne (E := E) : 𝔸f E) else 0) *
        (star (idem P) * (star (↑π⁻¹ : 𝔸f E) * x (lastSource, i.2) +
          (normNegOne (E := E) : 𝔸f E) * star (residueOverN (y i.2))) -
            star (idem P) * x (lastSource, i.2)) := by
  ext1 u
  rcases i with ⟨i₁, a⟩
  by_cases huS : star u ∈ P
  · have h_mulVec : evalAt u (((neighbourUnitary X X'' hπ : Matrix _ _ (𝔸f E)) *ᵥ
        fun l : PairIndex X X'' ↦ x (l, a)) i₁) =
        evalAt u (x (i₁, a)) +
          (if i₁ = lastSource then 1
            else if i₁ = lastTarget then star (normNegOne (E := E) : 𝔸f E) u else 0) *
          (star (↑π⁻¹ : 𝔸f E) u - 1) * evalAt u (x (lastSource, a)) := by
      simp only [mulVec, dotProduct, map_sum, map_mul,
        evalAt_neighbourUnitary_of_star_mem hπ huS, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, add_mul, Finset.sum_add_distrib]
      rw [Fintype.sum_eq_single i₁ (fun l hl ↦ by simp [hl]),
        Fintype.sum_eq_single lastSource (fun l hl ↦ by simp [localGlueProj, hl])]
      rcases i₁ with (b | ⟨⟩) | (b | ⟨⟩) <;> simp [localGlueProj, evalAt_apply, mul_comm]
    have h_norm_u : star (normNegOne (E := E) : 𝔸f E) u * (normNegOne (E := E) : 𝔸f E) u = -1 :=
      congrArg (evalAt u) (star_normNegOne_mul_self (E := E))
    have h_lhs : ((star (idem P) : 𝔸f E) * (((neighbourUnitary X X'' hπ : Matrix _ _ (𝔸f E)) *ᵥ
        fun l : PairIndex X X'' ↦ x (l, a)) i₁ + neighbourTranslation X X'' y (i₁, a))) u =
        evalAt u (((neighbourUnitary X X'' hπ : Matrix _ _ (𝔸f E)) *ᵥ
          fun l : PairIndex X X'' ↦ x (l, a)) i₁) + neighbourTranslation X X'' y (i₁, a) u := by
      simp [star_idem, huS, evalAt_apply]
    rw [h_lhs, h_mulVec]
    rcases i₁ with (b | ⟨⟩) | (b | ⟨⟩) <;>
      simp only [neighbourTranslation, Sum.elim_inl, Sum.elim_inr, star_idem, Set.mem_preimage,
        idem_apply, Finset.mem_coe, huS, evalAt_apply, finAdele_mul_apply, finAdele_add_apply,
        finAdele_sub_apply, finAdele_neg_apply, finAdele_zero_apply, Sum.inr_ne_inl, Sum.inl_ne_inr,
        Sum.inl.injEq, Sum.inr.injEq, ↓reduceIte, Pi.zero_apply, one_mul, zero_mul, add_zero]
    · ring
    · linear_combination -(star (residueOverN (y a)) u) * h_norm_u
  · rcases i₁ with (b | ⟨⟩) | (b | ⟨⟩) <;> simp [star_idem, huS]

/-- Let the prime `N` be split as `P` and its conjugate and `π` split squarefree for `N` at `P`.
`kroneckerOne` lets the unitary `γ` act on each column. Let `η = normNegOne` have norm `-1`. For
residues `y` modulo `N` at `P`, `n y = neighbourTranslation X X'' y` has row `η ȳ / N` at `e`, row
`-ȳ / N` at `e''` and zero elsewhere. At the places conjugate to `P`, `γ x + n y` is integral for
exactly one `y` if `x` is integral there, and for none otherwise. -/
lemma exists_add_neighbourTranslation_mem_iff [Fact N.Prime] (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (x : PairIndex X X'' × X' → 𝔸f E) :
    ∃ y₀ : X' → P → ZMod N, ∀ y : X' → P → ZMod N,
      kroneckerOne X' (PairIndex X X'') (neighbourUnitary X X'' hπ) • x +
          neighbourTranslation X X'' y ∈ integralBox (PairIndex X X'' × X')
          (star ⁻¹' (P : Set (FinPlace E))) ↔
        x ∈ integralBox (PairIndex X X'' × X') (star ⁻¹' (P : Set (FinPlace E))) ∧ y₀ = y := by
  -- In column `a`, take the residues attached to the entry of `x` at `lastSource`.
  choose y₀ hy₀ using fun a : X' ↦ exists_class_star_idem_mul_mem_iff hP hπ (x (lastSource, a))
  refine ⟨y₀, fun y ↦ ?_⟩
  have h_axis_mem (b : PairIndex X X'') :
      (if b = lastSource then 1
        else if b = lastTarget then star (normNegOne (E := E) : 𝔸f E) else 0) ∈ Ô E := by
    split_ifs <;> simp [one_mem, zero_mem, star_mem_Ô normNegOne_mem]
  simp only [mem_integralBox, ← star_idem, Pi.add_apply, kroneckerOne_smul,
    star_idem_mul_neighbourUnitary_add_translation hπ]
  refine ⟨fun h ↦ ?_, fun ⟨hx, hy⟩ i ↦ ?_⟩
  · -- The row at `lastSource` decides the residues; then, times `j̄`, all entries differ from those
    -- of `x` by integral adeles.
    have h_row (a : X') : star (idem P) * (star (↑π⁻¹ : 𝔸f E) * x (lastSource, a) +
        (normNegOne (E := E) : 𝔸f E) * star (residueOverN (y a))) ∈ Ô E := by
      simpa using h (lastSource, a)
    have h_residues (a : X') : star (idem P) * x (lastSource, a) ∈ Ô E ∧ y₀ a = y a :=
      (hy₀ a (y a)).1 (h_row a)
    refine ⟨fun i ↦ ?_, funext fun a ↦ (h_residues a).2⟩
    exact (add_mem_cancel_right
      (mul_mem (h_axis_mem i.1) (sub_mem (h_row i.2) (h_residues i.2).1))).1 (h i)
  · exact add_mem (hx i) (mul_mem (h_axis_mem i.1)
      (sub_mem ((hy₀ i.2 (y i.2)).2 ⟨hx (lastSource, i.2), congrFun hy i.2⟩)
        (hx (lastSource, i.2))))

end KroneckerAndBox

end LocalSplitBlock

/-! ### Glued translates on the two edges and Weil-operator factorization -/

section WeilGluing

variable [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X'] [Fintype X''] [DecidableEq X'']
  {N : ℕ} {P : Finset (FinPlace E)} {π : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E}
  {κ : PairIndex X X'' → 𝔸f E}

variable (E X X' X'') in
/-- The space `Hom (X', (X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit))` of the standard spaces, the target of
`arrowTensor` for a pair of standard edges. -/
abbrev stdPairSpace : Space E (PairIndex X X'' × X') (homSigns 1 (-1 ⊕ᵥ 1)) :=
  (stdSpace E X').hom (flipSum (stdSpace E (X ⊕ Unit)) (stdSpace E (X'' ⊕ Unit)))

/-- The glued translate attached to a pair of finite adelic matrices `t = (t₁, t₂)`: translate the
vacuum of the edge `Hom(X ⊕ Unit, X')` by `t₁` and that of `Hom(X', X'' ⊕ Unit)` by `t₂`, and apply
`doubleLiftGluing` (the sum over residues modulo `N` at `P`) to the tensor of the two. -/
def gluedTranslate (N : ℕ) [Fact N.Prime] (P : Finset (FinPlace E))
    (t : (X' × (X ⊕ Unit) → 𝔸f E) × ((X'' ⊕ Unit) × X' → 𝔸f E)) :
    ((stdSpace E (X ⊕ Unit)).hom (stdSpace E X')).finitePart ⊗[ℂ]
      ((stdSpace E X').hom (stdSpace E (X'' ⊕ Unit))).finitePart :=
  doubleLiftGluing X X' P N X''
    (((stdSpace E (X ⊕ Unit)).hom (stdSpace E X')).heisenbergFinPart t.1
        ⟨((stdSpace E (X ⊕ Unit)).hom (stdSpace E X')).vacElem, vacElem_mem_finitePart⟩ ⊗ₜ
      ((stdSpace E X').hom (stdSpace E (X'' ⊕ Unit))).heisenbergFinPart t.2
        ⟨((stdSpace E X').hom (stdSpace E (X'' ⊕ Unit))).vacElem, vacElem_mem_finitePart⟩)

/-- There is a constant `C` such that, for every `n` prime to `N` and every proposition `p`, the map
`L` sends each translate of the vacuum of `Hom(V', V⁻ ⊕ V'')` by a matrix `y`, whose row `i` times
`d i` is integral away from `n`, to an admissible combination of the vectors
`C • gluedTranslate N P (t₁, t₂)`, where `β̄ t₁`, `β̄ t₂` are integral away from `n`. The
coefficients are integral away from `n` after multiplication by the number of classes of integral
matrices modulo `β`, and if `p` holds their absolute sum is at most `1` under every automorphism
of `ℂ`. -/
def IsAdmissibleEval {ι ι' ι'' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    [Fintype ι''] [DecidableEq ι''] {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {ε'' : ι'' → ℤˣ} {V : Space E ι ε}
    {V' : Space E ι' ε'} {V'' : Space E ι'' ε''} (N : ℕ) [Fact N.Prime] (P : Finset (FinPlace E))
    (β : Ô E) (L : 𝒮 (V'.hom (flipSum V V'')) →
      ((stdSpace E (X ⊕ Unit)).hom (stdSpace E X')).finitePart ⊗[ℂ]
        ((stdSpace E X').hom (stdSpace E (X'' ⊕ Unit))).finitePart)
    (d : ι ⊕ ι'' → 𝔸f E) : Prop :=
  ∃ C : ℂ, ∀ (n : ℕ) (p : Prop), N.Coprime n →
    ∀ y ∈ weightedTranslations n fun i : (ι ⊕ ι'') × ι' ↦ d i.1,
      IsAdmissibleCombination
        (fun t : (X' × (X ⊕ Unit) → 𝔸f E) × ((X'' ⊕ Unit) × X' → 𝔸f E) ↦
          C • gluedTranslate N P t)
        (translations (X' × (X ⊕ Unit)) n (star (β : 𝔸f E)) ×ˢ
          translations ((X'' ⊕ Unit) × X') n (star (β : 𝔸f E))) n
        (Nat.card (PairIndex X X'' × X' → Ô E ⧸ Ideal.span {β})) p 1
        (L ((V'.hom (flipSum V V'')).finHeisenbergOp y (V'.hom (flipSum V V'')).vacElem))

section Edges

variable {ι ι' ι'' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype ι''] [DecidableEq ι''] {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {ε'' : ι'' → ℤˣ}
  {V : Space E ι ε} {V' : Space E ι' ε'} {V'' : Space E ι'' ε''}

/-- On a pure tensor `Φ ⊗ Ψ` of data on the two edges, `arrowTensor` is `arrowProduct Φ Ψ`. -/
lemma arrowTensor_tmul (Φ : (V.hom V').finitePart) (Ψ : (V'.hom V'').finitePart) :
    arrowTensor (Φ ⊗ₜ[ℂ] Ψ) = arrowProduct (Φ : 𝒮 (V.hom V')) (Ψ : 𝒮 (V'.hom V'')) :=
  rfl

/-- The translate by `z` of the vacuum of `Hom(V', V⁻ ⊕ V'')` is the square of `semichar` of the
first block of `z` times the image under `arrowTensor` of the tensor of two translates. These are
the vacuum of `Hom(V, V')` translated by `normNegOne` (the unit of norm `-1`) times the adjoint of
the first block of `z`, and the vacuum of `Hom(V', V'')` translated by the second block of `z`. -/
lemma finHeisenbergOp_vacElem_eq_smul_arrowTensor (z : (ι ⊕ ι'') × ι' → 𝔸f E) :
    (V'.hom (flipSum V V'')).finHeisenbergOp z (V'.hom (flipSum V V'')).vacElem =
      semichar (fun i : ι' × ι ↦ z (Sum.inl i.2, i.1)) ^ 2 • arrowTensor
        ((V.hom V').heisenbergFinPart
            (fun i : ι' × ι ↦ (normNegOne (E := E) : 𝔸f E) * star (z (Sum.inl i.2, i.1)))
            ⟨(V.hom V').vacElem, vacElem_mem_finitePart⟩ ⊗ₜ[ℂ]
          (V'.hom V'').heisenbergFinPart (fun i : ι'' × ι' ↦ z (Sum.inr i.1, i.2))
            ⟨(V'.hom V'').vacElem, vacElem_mem_finitePart⟩) := by
  rw [arrowTensor_tmul, heisenbergFinPart_apply_coe, heisenbergFinPart_apply_coe,
    ← arrowProduct_vacElem, finHeisenbergOp_arrowProduct]

end Edges

open scoped Classical in
/-- Let `N` be a prime that splits as `N = π π̄`. Let `t` be a tensor of finite data (`finitePart`)
on the two edges `Hom(X ⊕ Unit, X')` and `Hom(X', X'' ⊕ Unit)` of standard spaces. The map
`arrowTensor` joins it to one datum on `stdPairSpace`, the space
`Hom(X', (X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit))`. There the operator `doubleLiftGluing` (the sum over residues
`y` of the translation of the first datum by the last column `-y / N` and of the second by the last
row `-ȳ / N`) becomes the sum of the translations by `neighbourTranslation X X'' y`, the matrices
whose only nonzero rows are `η ȳ / N` and `-ȳ / N` at the two last basis vectors. -/
lemma arrowTensor_doubleLiftGluing [Fact N.Prime] (hπ : IsSplitSquarefree P (N : E) π)
    (t : ((stdSpace E (X ⊕ Unit)).hom (stdSpace E X')).finitePart ⊗[ℂ]
      ((stdSpace E X').hom (stdSpace E (X'' ⊕ Unit))).finitePart) :
    arrowTensor (doubleLiftGluing X X' P N X'' t) =
      ∑ y : X' → P → ZMod N,
        (stdPairSpace E X X' X'').finHeisenbergOp (neighbourTranslation X X'' y)
          (arrowTensor t) := by
  induction t with
  | add t t' ht ht' => simp [ht, ht', Finset.sum_add_distrib]
  | tmul Φ Ψ =>
    -- The adjoint, times the unit of norm `-1`, turns the first nonzero row of
    -- `neighbourTranslation y` into the last column `-y / N`; the second nonzero row is the last
    -- row `-ȳ / N`.
    have h_column (y : X' → P → ZMod N) :
        (fun q : X' × (X ⊕ Unit) ↦ (normNegOne (E := E) : 𝔸f E) *
          star (neighbourTranslation X X'' y (Sum.inl q.2, q.1))) = poleColumn X y := by
      ext ⟨a, i | i⟩ : 1 <;> simp [neighbourTranslation, ← mul_assoc, mul_comm _ (star _)]
    have h_row (y : X' → P → ZMod N) :
        (fun q : (X'' ⊕ Unit) × X' ↦ neighbourTranslation X X'' y (Sum.inr q.1, q.2)) =
          poleRow X'' y := by
      ext ⟨i | i, a⟩ : 1 <;> simp [neighbourTranslation]
    have h_phase (y : X' → P → ZMod N) :
        semichar (fun q : X' × (X ⊕ Unit) ↦ neighbourTranslation X X'' y (Sum.inl q.2, q.1)) = 1 :=
      semichar_eq_one_of_smul_eq hπ <|
        funext fun q ↦ congrFun (star_idem_smul_neighbourTranslation y) (Sum.inl q.2, q.1)
    simp only [doubleLiftGluing, LinearMap.sum_apply, map_sum, map_tmul, arrowTensor_tmul,
      finHeisenbergOp_arrowProduct, h_column, h_row, h_phase, one_pow, one_smul,
      heisenbergFinPart_apply_coe]

open scoped Classical in
/-- Let `N` be a prime that splits as `N = π π̄`, where `π` is a uniformiser at the places of `P`
and a unit elsewhere. Let `z` be a matrix on `PairIndex X X''` times `X'` whose rows have
denominator at most `β` in the first block and `β̄` in the second (`selfOrConj β`), away from `n`.
In `stdPairSpace`, the space `Hom(X', (X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit))`, add up over residues `y` modulo
`N` at `P` the translates, by `neighbourTranslation X X'' y`, of the translate of the vacuum by `z`.
The sum is a root of unity times the image under `arrowTensor` of `gluedTranslate N P (t₁, t₂)`, the
glued tensor of the translates by `t₁`, `t₂` of the vacua of the two edges, for some `t₁`, `t₂` with
`β̄ t₁`, `β̄ t₂` integral away from `n`. -/
lemma exists_sum_finHeisenbergOp_neighbourTranslation_eq [Fact N.Prime]
    (hπ : IsSplitSquarefree P (N : E) π) {n : ℕ} {z : PairIndex X X'' × X' → 𝔸f E}
    (hz : z ∈ weightedTranslations n fun i : PairIndex X X'' × X' ↦ selfOrConj β i.1) :
    ∃ ζ : ℂ, IsOfFinOrder ζ ∧
      ∃ t₁ ∈ translations (X' × (X ⊕ Unit)) n (star (β : 𝔸f E)),
        ∃ t₂ ∈ translations ((X'' ⊕ Unit) × X') n (star (β : 𝔸f E)),
          ∑ y : X' → P → ZMod N, (stdPairSpace E X X' X'').finHeisenbergOp
            (neighbourTranslation X X'' y)
              ((stdPairSpace E X X' X'').finHeisenbergOp z (stdPairSpace E X X' X'').vacElem) =
            ζ • arrowTensor (gluedTranslate N P (t₁, t₂)) := by
  -- `z` splits into `t₁` on the first edge, through the adjoint, and `t₂` on the second.
  let t₁ : X' × (X ⊕ Unit) → 𝔸f E := fun i ↦
    (normNegOne (E := E) : 𝔸f E) * star (z (Sum.inl i.2, i.1))
  have ht₁ : t₁ ∈ translations (X' × (X ⊕ Unit)) n (star (β : 𝔸f E)) :=
    star_mem_weightedTranslations normNegOne_mem hz fun i : X' × (X ⊕ Unit) ↦ (Sum.inl i.2, i.1)
  let t₂ : (X'' ⊕ Unit) × X' → 𝔸f E := fun i ↦ z (Sum.inr i.1, i.2)
  have ht₂ : t₂ ∈ translations ((X'' ⊕ Unit) × X') n (star (β : 𝔸f E)) := fun i ↦
    hz (Sum.inr i.1, i.2)
  refine ⟨semichar (fun i : X' × (X ⊕ Unit) ↦ z (Sum.inl i.2, i.1)) ^ 2, (isOfFinOrder_ψf _).pow,
    t₁, ht₁, t₂, ht₂, ?_⟩
  simp only [t₁, t₂, finHeisenbergOp_vacElem_eq_smul_arrowTensor, gluedTranslate,
    arrowTensor_doubleLiftGluing hπ, map_smul, smul_sum]

omit [WeilData E] in
/-- Away from `N`, the index of the sublattice of `Ô ^ (PairIndex X X'' × X')` stabilized by
`scalingUnitary hκ ⊗ 1` divides `#(PairIndex X X'' × X' → Ô E ⧸ (β))`: any integral matrix whose
conjugate entries are multiples of `β` has entries divisible by `β̄`, and `β̄ κ_j` is integral. -/
lemma index_scalingUnitary_dvd (hκ : IsScalingAtM N β δ κ) :
    let L := stdLattice E (PairIndex X X'' × X')
    ((L.comap (kroneckerOne X' (PairIndex X X'') (scalingUnitary hκ) :
        Matrix _ _ (𝔸f E)).mulVecLin.toAddMonoidHom).addSubgroupOf L).index ∣
      Nat.card (PairIndex X X'' × X' → Ô E ⧸ Ideal.span {β}) := by
  intro L
  set H : AddSubgroup L :=
    (L.comap (kroneckerOne X' (PairIndex X X'') (scalingUnitary hκ) :
      Matrix _ _ (𝔸f E)).mulVecLin.toAddMonoidHom).addSubgroupOf L
  -- Map `z ∈ L` to the residue classes of `star (z j)` modulo `(β)`.
  let φ : L →+ (PairIndex X X'' × X' → Ô E ⧸ Ideal.span {β}) :=
    AddMonoidHom.mk' (fun z j ↦ Ideal.Quotient.mk (Ideal.span {β}) (star ⟨z.val j, z.2 j⟩))
      fun z w ↦ by
        ext j
        exact congrArg (Ideal.Quotient.mk _) (Subtype.ext (by simp [star_add]))
  have h_ker_le : φ.ker ≤ H := by
    intro z hz j
    have hj : Ideal.Quotient.mk (Ideal.span {β}) (star ⟨z.val j, z.2 j⟩) = 0 := congrFun hz j
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 hj)
    have hz_eq : z.val j = star (β : 𝔸f E) * star (q : 𝔸f E) := by
      have h_star := congrArg (fun x : Ô E ↦ star (x : 𝔸f E)) hq
      simpa [star_star, star_mul'] using h_star
    change (kroneckerOne X' (PairIndex X X'') (scalingUnitary hκ) • z.val) j ∈ Ô E
    rw [kroneckerOne_scalingUnitary_smul, hz_eq, ← mul_assoc, mul_comm (κ j.1)]
    exact mul_mem (hκ.star_mul_mem j.1) (star_mem_Ô q.2)
  exact (AddSubgroup.dvd_index_map H h_ker_le).trans (AddSubgroup.index_dvd_card _)

open scoped Classical in
/-- Above `N`, the Weil operator `Z.ω (1, γ ⊗ 1)` on any translate `Z.finHeisenbergOp w Z.vacElem`
with `w` integral at `P ∪ P̄` acts through `Z.projOn (star ⁻¹' P)`: by
`omega_schrodingerOp_of_mem_supportedOn` and `exists_add_neighbourTranslation_mem_iff`, it equals a
fixed scalar `C_N` times the sum over residue matrices `r : X' → P → ZMod N` of the Heisenberg
translates by `neighbourTranslation X X'' r`. -/
lemma omega_neighbourUnitary_finHeisenbergOp_vacElem [Fact N.Prime] (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) {n : ℕ} (hn : N.Coprime n)
    {w : PairIndex X X'' × X' → 𝔸f E}
    (hw : w ∈ weightedTranslations n fun j : PairIndex X X'' × X' ↦ selfOrConj β j.1) :
    let Z := stdPairSpace E X X' X''
    let S : Set (FinPlace E) := star ⁻¹' (P : Set (FinPlace E))
    let g_N := kroneckerOne X' (PairIndex X X'') (neighbourUnitary X X'' hπ)
    Z.ω (1, g_N) (Z.finHeisenbergOp w Z.vacElem) =
      starRingEnd ℂ (chiAdelic (detOn S g_N.val)) •
        ∑ r : X' → P → ZMod N,
          Z.finHeisenbergOp (neighbourTranslation X X'' r) (Z.finHeisenbergOp w Z.vacElem) := by
  intro Z S g_N
  have hS : S.IsConjDisjoint :=
    Set.disjoint_left.2 fun u (hu : star u ∈ P) (hu' : star (star u) ∈ P) ↦
      hπ.star_notMem u (by simpa using hu') hu
  have hg_N : g_N ∈ supportedOn _ S := Gf.mem_supportedOn.2 fun u hu huS ↦
    kroneckerOne_atPlace_eq_one _ <| Gf.mem_supportedOn.1 (ofSplitPlaces_mem_supportedOn _ _) u
      (by simpa [S] using huS) (by simpa [S] using hu)
  -- Since `gcd(N, n) = 1` and `β, β̄` are units above `N`, `w` is integral at `S ∪ S̄ = P ∪ P̄`, so
  -- `Z.projOn S` fixes `Z.finHeisenbergOp w Z.vacElem`.
  have hw_box : w ∈ integralBox _ S.conjClosure := by
    intro j
    refine idem_mul_mem_Ô.2 fun u hu ↦ ?_
    have hP_or : u ∈ P ∨ star u ∈ P := by
      rcases hu with hu_in | hu_in
      · exact Or.inr hu_in
      · exact Or.inl (by simpa [S] using hu_in)
    have hN : ↑N ∈ u.asIdeal := (hP.natCast_mem_iff u).2 hP_or
    have h_le := hw j u (u.isPrime.notMem_of_isCoprime_of_mem hn.cast hN)
    simpa [v_selfOrConj_eq_one hκ j.1 hN] using h_le
  have h_proj : Z.projOn S (Z.finHeisenbergOp w Z.vacElem) = Z.finHeisenbergOp w Z.vacElem := by
    rw [Z.projOn_finHeisenbergOp_vacElem, ite_eq_left hw_box]
  -- Decompose `boxIndicator _ S ∘ g_N⁻¹` as the sum over residue classes `r` of Schrödinger
  -- translates by `neighbourTranslation X X'' r`; the Schrödinger phase vanishes since `r` is
  -- supported on `S` while `star r` is supported on `P` disjoint from `S`.
  have h_ind :
      (fun x : PairIndex X X'' × X' → 𝔸f E ↦ boxIndicator _ S (g_N⁻¹.val.val *ᵥ x)) =
      ∑ r : X' → P → ZMod N,
        schrodingerAct S (neighbourTranslation X X'' r) (boxIndicator _ S) := by
    ext x
    obtain ⟨x₀, rfl⟩ := MulAction.surjective g_N x
    have h_inv : g_N⁻¹.val.val *ᵥ (g_N • x₀) = x₀ := inv_smul_smul g_N x₀
    obtain ⟨r₀, hr₀⟩ := exists_add_neighbourTranslation_mem_iff (X' := X') hP hπ x₀
    rw [h_inv, Finset.sum_apply]
    have h_act (r : X' → P → ZMod N) :
        schrodingerAct S (neighbourTranslation X X'' r) (boxIndicator _ S) (g_N • x₀) =
          boxIndicator _ S (g_N • x₀ + neighbourTranslation X X'' r) := by
      have h_zero (v : PairIndex X X'' × X' → 𝔸f E) :
          idem S * (star (neighbourTranslation X X'' r) ⬝ᵥ v) = 0 := by
        rw [← smul_eq_mul, ← smul_dotProduct, ← star_idem_smul_neighbourTranslation r, star_smul,
          star_star, smul_smul,
          show idem S = star (idem (P : Set (FinPlace E))) from (star_idem _).symm,
          mul_comm (star _), idem_mul_star hπ.isConjDisjoint, zero_smul, zero_dotProduct]
      simp [schrodingerAct, h_zero]
    simp only [h_act, boxIndicator, S, g_N, hr₀]
    by_cases hx₀ : x₀ ∈ integralBox _ (star ⁻¹' (P : Set (FinPlace E)))
    · simp only [hx₀, ↓reduceIte, true_and, Finset.sum_ite_eq, Finset.mem_univ]
    · simp only [hx₀, ↓reduceIte, false_and, Finset.sum_const_zero]
  calc Z.ω (1, g_N) (Z.finHeisenbergOp w Z.vacElem)
      = Z.ω (1, g_N) (Z.schrodingerOp S (boxIndicator _ S) (Z.finHeisenbergOp w Z.vacElem)) := by
          rw [Z.schrodingerOp_boxIndicator hS, h_proj]
    _ = starRingEnd ℂ (chiAdelic (detOn S g_N.val)) •
          Z.schrodingerOp S (fun x ↦ boxIndicator _ S (g_N⁻¹.val.val *ᵥ x))
            (Z.finHeisenbergOp w Z.vacElem) :=
          Z.omega_schrodingerOp_of_mem_supportedOn hS hg_N _
    _ = starRingEnd ℂ (chiAdelic (detOn S g_N.val)) •
          ∑ r : X' → P → ZMod N,
            Z.finHeisenbergOp (neighbourTranslation X X'' r) (Z.finHeisenbergOp w Z.vacElem) := by
          rw [h_ind, map_sum, FunLike.coe_sum, Finset.sum_apply]
          congr 1
          refine Finset.sum_congr rfl fun r _ ↦ ?_
          have h_supp : idem S.conjClosure • neighbourTranslation X X'' r =
              neighbourTranslation X X'' r := by
            rw [← star_idem_smul_neighbourTranslation r, smul_smul, star_idem]
            congr 1
            ext1 u
            by_cases hu : star u ∈ P <;> simp [S, Set.conjClosure, hu]
          have h_semi : semichar (neighbourTranslation X X'' r) = 1 :=
            semichar_eq_one_of_smul_eq hπ (star_idem_smul_neighbourTranslation r)
          rw [Z.schrodingerOp_schrodingerAct_boxIndicator hS, h_supp, h_proj]
          conv_rhs => rw [finHeisenbergOp, _root_.smul_apply, h_semi, one_smul]

end WeilGluing

end PlacewiseNeighbour

/-! ## Membership in a glued lattice -/

section GluedLattice

open NumberField Matrix Valued

variable {n n₀ : Type} [Fintype n]

/-- Let the grading `Y` present the space `V` as `n₀ ⊕ Unit` plus a string of `m` vectors, and
suppose that the columns of `V.xFin`, the finite point of `V`, span the lattice of
`gradedLatticeBasis` for `a`, `π` and `u`, in which the last vector of `n₀ ⊕ Unit` is glued to the
middle of the string. Let `vec` have the component `x` in `n₀ ⊕ Unit`, the coordinate
`u * (π⁻¹ * x e + c)` at the middle vector of the string, where `e = Sum.inr ()` is the last index,
and `0` at the other vectors of the string. If `c`, `π̄ * x e` and the other entries of `x` are
integral, then `vec` lies in that lattice. -/
lemma inv_xFin_mulVec_mem_of_spansLattice {E : Type} [Field E] [CMType E]
    [DecidableEq n] [Finite n₀] [DecidableEq n₀]
    {s : n → ℤˣ} {N : E} {m : ℕ} {a π : (𝔸f E)ˣ} {u : unitary (𝔸f E)} {V : Space E n s}
    {Y : Grading V N (n₀ ⊕ Unit) m} (hL : Y.SpansLattice a π u) (hm : Odd m) {x : n₀ ⊕ Unit → 𝔸f E}
    {c : 𝔸f E} (hx_int : ∀ i : n₀, x (Sum.inl i) ∈ Ô E)
    (hx_last : star (π : 𝔸f E) * x (Sum.inr ()) ∈ Ô E)
    (hc : c ∈ Ô E) {vec : n → 𝔸f E}
    (h_gradeZero : ∀ i : n₀ ⊕ Unit, vec (Y.indexEquiv (Sum.inl i)) = x i)
    (h_string : ∀ b : Fin m, vec (Y.indexEquiv (Sum.inr b)) =
      if 2 * b.val + 1 = m then u * (↑π⁻¹ * x (Sum.inr ()) + c) else 0) :
    V.xFin⁻¹.val *ᵥ vec ∈ stdLattice E n := by
  have := Fintype.ofFinite n₀
  obtain ⟨k, hk, h_point⟩ : ∃ k ∈ intGL n (Ô E),
      V.xFin.val = gradedLatticeBasis Y.indexEquiv a π u * k.val := hL
  -- The coordinates of `vec` in `gradedLatticeBasis`: `x` on `n₀`, `π̄ * x e` at the glue vector,
  -- `c` at the middle vector of the string, and `0` elsewhere.
  let y : (n₀ ⊕ Unit) ⊕ Fin m → 𝔸f E :=
    (x ∘ Sum.inl ⊕ᵥ fun _ ↦ star (π : 𝔸f E) * x (Sum.inr ())) ⊕ᵥ
      fun b ↦ if 2 * b.val + 1 = m then c else 0
  have hy_int : y ∘ Y.indexEquiv.symm ∈ stdLattice E n := fun j ↦ by
    obtain ⟨(i | i) | b, rfl⟩ := Y.indexEquiv.surjective j <;>
      simp [y, hx_int, hx_last, hc, ite_mem]
  have h_cancel : star (↑π⁻¹ : 𝔸f E) * star (π : 𝔸f E) = 1 := by simp [← star_mul]
  have h_basis : vec = gradedLatticeBasis Y.indexEquiv a π u *ᵥ (y ∘ Y.indexEquiv.symm) := by
    funext j
    obtain ⟨i, rfl⟩ := Y.indexEquiv.surjective j
    simp only [gradedLatticeBasis, ite_eq_left hm, reindex_apply, submatrix_mulVec_equiv]
    rcases i with (i | i) | b
    · simp [y, h_gradeZero, fromBlocks_mulVec, mulVec_diagonal]
    · simp [y, h_gradeZero, fromBlocks_mulVec, mulVec_diagonal, ← mul_assoc, h_cancel]
    · -- Only the middle vector of the string is fixed by the reversal, and there the glue vector
      -- contributes `u (π̄ π)⁻¹ π̄ x e = u π⁻¹ x e`.
      have h_middle : b = b.rev ↔ 2 * b.val + 1 = m := by grind
      have h_glue : (u : 𝔸f E) * (↑π⁻¹ * star (↑π⁻¹ : 𝔸f E)) * (star (π : 𝔸f E) * x (Sum.inr ())) =
          u * (↑π⁻¹ * x (Sum.inr ())) := by
        linear_combination u * ↑π⁻¹ * x (Sum.inr ()) * h_cancel
      by_cases hb : 2 * b.val + 1 = m <;>
        simp [y, h_string, fromBlocks_mulVec, mulVec, dotProduct, h_middle,
          hb, mul_add, h_glue]
  -- The point of `V` is `gradedLatticeBasis * k` with `k` integral and integrally invertible.
  have h_inv : V.xFin⁻¹.val * gradedLatticeBasis Y.indexEquiv a π u = k⁻¹.val := by
    rw [Units.inv_mul_eq_iff_eq_mul, Units.eq_mul_inv_iff_mul_eq, h_point]
  rw [h_basis, mulVec_mulVec, h_inv]
  exact IsIntMatrix.mulVec (mem_intGL.1 hk).2 hy_int

end GluedLattice

/-! ## Lifting the neighbour unitary and admissible evaluation of a double lift -/

section AdmissibleEvaluation

open Matrix Space WeilData Kronecker Exchange Finset Weil Valued Prod Grading Splitting stdLattice
  DoubleLiftData TensorProduct PairIndex NumberField

variable {E X X' X'' : Type} [Field E] [CMType E] [WeilData E] [Fintype X] [DecidableEq X]
  [Fintype X'] [DecidableEq X'] [Fintype X''] [DecidableEq X'']

section Lift

variable {ι ι' ι'' μ q : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype ι''] [DecidableEq ι''] [Fintype μ] [DecidableEq μ] [Fintype q] [DecidableEq q]
  {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {ε'' : ι'' → ℤˣ} {V : Space E ι ε} {V' : Space E ι' ε'}
  {V'' : Space E ι'' ε''} {N m m' m'' : ℕ} {Y : Grading V N (X ⊕ Unit) m}
  {Y' : Grading V' N (X' ⊕ Unit) m'}

variable (E) in
/-- The finite idele by which negating the form of a space scales its point: the finite part of
the conjugate of `flipIdele` for `η = normNegOne`, a unit of `Ô E` with `η̄ η = -1`. -/
def flipScale : (𝔸f E)ˣ :=
  Units.map (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)).toMonoidHom
    (star (flipIdele normNegOne 1))

/-- The idele `flipScale E` is the conjugate of `η = normNegOne` times `ᾱ α⁻¹`, where `α` is the
finite idele of the Weil data. -/
lemma coe_flipScale :
    (flipScale E : 𝔸f E) = star (normNegOne (E := E) : 𝔸f E) * ↑(star α * α⁻¹ : (𝔸f E)ˣ) := by
  simp [flipScale, val_flipIdele, mul_assoc]

variable (V V'') in
/-- The inverse of the finite point of `V⁻ ⊕ V''` is block diagonal, with blocks the inverse point
of `V` divided by `flipScale E` and the inverse point of `V''`. -/
lemma inv_xFin_flipSum :
    (flipSum V V'').xFin⁻¹.val =
      fromBlocks ((flipScale E)⁻¹.val • V.xFin⁻¹.val) 0 0 V''.xFin⁻¹.val := by
  simp [flipScale, xFin, Space.sum, flipSpace, ← map_inv, ← smul_eq_mul_diagonal,
    ← Matrix.ext_iff]

variable (V V'') in
/-- A vector `y` of finite adeles indexed by `ι ⊕ ι''` lies in the lattice of `V⁻ ⊕ V''`, that is
`(flipSum V V'').xFin⁻¹ *ᵥ y ∈ stdLattice`, exactly if its first block, divided by `flipScale E`,
lies in the lattice of `V` and its second block lies in the lattice of `V''`. -/
lemma inv_xFin_flipSum_mulVec_mem_iff (y : ι ⊕ ι'' → 𝔸f E) :
    (flipSum V V'').xFin⁻¹.val *ᵥ y ∈ stdLattice E (ι ⊕ ι'') ↔
      V.xFin⁻¹.val *ᵥ ((flipScale E)⁻¹.val • y ∘ Sum.inl) ∈ stdLattice E ι ∧
        V''.xFin⁻¹.val *ᵥ (y ∘ Sum.inr) ∈ stdLattice E ι'' := by
  simp only [inv_xFin_flipSum, fromBlocks_mulVec, mem_stdLattice, Sum.forall, Sum.elim_inl,
    Sum.elim_inr, zero_mulVec, add_zero, zero_add, smul_mulVec, mulVec_smul]

/-- The rows of the finite part of the point of `V'` at the basis vectors of `X' ⊕ Unit`. -/
def _root_.New.Grading.gradeZeroRows (Y' : Grading V' N (X' ⊕ Unit) m') :
    Matrix (X' ⊕ Unit) ι' (𝔸f E) :=
  (inclMatrix (𝔸f E) (Y'.indexEquiv ∘ Sum.inl))ᵀ * V'.xFin.val

omit [WeilData E] [Fintype X'] in
/-- Let `Y'` present `V'` as `X' ⊕ Unit` plus a string of even length `m'`, and suppose that the
finite point of `V'` spans the lattice of `gradedLatticeBasis` for `a`, `π`, `u`. For even length
this basis is the identity on `X' ⊕ Unit` and scales the string vectors by `u a⁻¹` or `u ā`. Then
the rows of the point at `X' ⊕ Unit` are integral. -/
lemma _root_.New.Grading.isIntMatrix_gradeZeroRows [Finite X'] {a π : (𝔸f E)ˣ} {u : unitary (𝔸f E)}
    (hL : Y'.SpansLattice a π u) (h_even : ¬Odd m') : IsIntMatrix (Ô E) Y'.gradeZeroRows := by
  have := Fintype.ofFinite X'
  obtain ⟨k, hk, h_point⟩ : ∃ k ∈ intGL ι' (Ô E),
      V'.xFin.val = gradedLatticeBasis Y'.indexEquiv a π u * k.val := hL
  intro l j
  have h_row : Y'.gradeZeroRows l j = k.val (Y'.indexEquiv (Sum.inl l)) j := by
    -- The row of the graded basis at an index of `X' ⊕ Unit` is that of the identity matrix.
    cases l <;>
      simp [gradeZeroRows, h_point, gradedLatticeBasis, Matrix.mul_apply, inclMatrix,
        Matrix.one_apply, reindex_equiv Y'.indexEquiv, h_even]
  rw [h_row]
  exact (mem_intGL.1 hk).1 _ j

omit [WeilData E] [Fintype X'] in
/-- The adjoint of the rows of the point of `V'` at `X' ⊕ Unit` consists of the columns of the
inverse point at these basis vectors, since the form of `V'` is `1` on them. -/
lemma _root_.New.Grading.conjTranspose_gradeZeroRows
    [Finite X'] (Y' : Grading V' N (X' ⊕ Unit) m') :
    Y'.gradeZeroRowsᴴ = V'.xFin⁻¹.val * inclMatrix (𝔸f E) (Y'.indexEquiv ∘ Sum.inl) := by
  have := Fintype.ofFinite X'
  -- The inverse of the point is its adjoint times the Gram matrix, which is `1` on `X' ⊕ Unit`.
  simp [gradeZeroRows, inv_eq_left_inv V'.gram_xFin, ← Matrix.ext_iff, Matrix.mul_apply, Y'.gram_eq,
    gradedGram, inclMatrix, Matrix.one_apply, reindex_equiv Y'.indexEquiv]

namespace DoubleLiftData

-- `D` is a pair of edges `Y → Y' → Y''` between the graded spaces `V`, `V'`, `V''`, where `q`
-- indexes the hyperbolic planes in grade zero.
variable {Y'' : Grading V'' N μ m''} (D : DoubleLiftData (X'' ⊕ Unit) q Y Y' Y'')
  {P : Finset (FinPlace E)} {π : (𝔸f E)ˣ} (hπ : IsSplitSquarefree P (N : E) π)
  (u : unitary (𝔸f E)) (κ : PairIndex X X'' → 𝔸f E)

/-- The vector of grade zero in `V⁻ ⊕ V''`, in rational coordinates, with the component `κ x` in
`X⁻ ⊕ X''` and the coefficient `u c` at the second basis vector of each plane; this coefficient
and the component in `X⁻` are multiplied by `flipScale E`. -/
def liftVector (c : 𝔸f E) (x : PairIndex X X'' → 𝔸f E) : ι ⊕ ι'' → 𝔸f E :=
  D.zeroPart.incl.map (algebraMap E (𝔸f E)) *ᵥ
    ((0 ⊕ᵥ fun _ ↦ flipScale E * u * c) ⊕ᵥ
      ((fun _ : X ⊕ Unit ↦ (flipScale E : 𝔸f E)) ⊕ᵥ (1 : X'' ⊕ Unit → 𝔸f E)) * κ * x)

variable (π) in
/-- Every neighbour vector `(c, x)`, that is, every solution of the gluing congruences
`IsNeighbourVector π δ c x`, has its lift `liftVector` in the lattice of `V⁻ ⊕ V''`. -/
def LiftsNeighbours (δ : 𝔸f E) : Prop :=
  ∀ (c : 𝔸f E) (x : PairIndex X X'' → 𝔸f E), IsNeighbourVector π δ c x →
    (flipSum V V'').xFin⁻¹.val *ᵥ D.liftVector u κ c x ∈ stdLattice E (ι ⊕ ι'')

/-- Where the inclusion of `X⁻ ⊕ X''` joins an index `b` to an index `i` of `V⁻ ⊕ V''`, the
denominator allowed at `i` has the valuations of the denominator allowed at `b` times `κ b`. -/
def MatchesDenominators (β : Ô E) : Prop :=
  ∀ (i : ι ⊕ ι'') (b : PairIndex X X''), D.zeroPart.incl i (Sum.inr b) ≠ 0 →
    ∀ w : FinPlace E, v (selfOrConj β i w) = v ((selfOrConj β b * κ b) w)

/-- The matrix whose columns are the lifts of the columns of `neighbourUnitary`, in the coordinates
of the lattice of `V⁻ ⊕ V''`. -/
def neighbourLift : Matrix (ι ⊕ ι'') (PairIndex X X'') (𝔸f E) :=
  (of fun j ↦ (flipSum V V'').xFin⁻¹.val *ᵥ
    D.liftVector u κ (neighbourCoeff X X'' P π j)
      ((neighbourUnitary X X'' hπ : Matrix _ _ (𝔸f E)).col j))ᵀ

variable (q P π) in
/-- The coefficients of the lifted columns at the second basis vectors of the planes. -/
def planeCoeff : Matrix q (PairIndex X X'') (𝔸f E) :=
  of fun _ j ↦ flipScale E * u * neighbourCoeff X X'' P π j

variable (q Y Y' Y'' P π) in
/-- The coordinates, in the isotropic frame of the splitting of `Hom (V', V⁻ ⊕ V'')`, of the
isotropic part of the columns of `latticeLift` (see `latticeLift_eq_latticeUnitary_add_isotropic`):
zero at the indices of positive grade and `planeCoeff ⊗ 1` at the planes. -/
def isotropicCoeff :
    Matrix ({r : (ι ⊕ ι'') × ι' // 0 < (Y.gradeOf ⊕ᵥ Y''.gradeOf) r.1 - Y'.gradeOf r.2} ⊕
      q × (X' ⊕ Unit)) (PairIndex X X'' × (X' ⊕ Unit)) (𝔸f E) :=
  fromRows 0 (planeCoeff (X := X) (X'' := X'') q P π u ⊗ₖ 1)

/-- The matrix `B` of the map `x ↦ A x R` from `Hom (X' ⊕ Unit, X⁻ ⊕ X'')` to
`Hom (V', V⁻ ⊕ V'')`, in the coordinates of the lattices, with `A = neighbourLift` and
`R = gradeZeroRows`. -/
def latticeLift : Matrix ((ι ⊕ ι'') × ι') (PairIndex X X'' × (X' ⊕ Unit)) (𝔸f E) :=
  D.neighbourLift hπ u κ ⊗ₖ Y'.gradeZeroRowsᵀ

variable {hπ u κ} {a : (𝔸f E)ˣ} {β : Ô E} {δ : 𝔸f E}

omit [Fintype X'] in
/-- For a finite set of places `P`, an idele `π`, a unitary adele `u` and scaling factors `κ`, let
`B = latticeLift` be the matrix of `x ↦ A x R`. Here the columns of `A` are the lifts to `V⁻ ⊕ V''`
of the columns of `neighbourUnitary`, and `R` consists of the rows of the point of `V'` at
`X' ⊕ Unit`. Then `Bᴴ` kills `stackedStringMapFin`, the finite coordinates of the map
`V' → V⁻ ⊕ V''` made of the adjoint of `stringMap` for `V → V'` and of `stringMap` for `V' → V''`;
these maps only move vectors of the strings. -/
lemma conjTranspose_latticeLift_mulVec_stackedStringMapFin [Finite X'] :
    (D.latticeLift hπ u κ)ᴴ *ᵥ stackedStringMapFin Y Y' Y'' = 0 := by
  have := Fintype.ofFinite X'
  -- `Bᴴ` first restricts a map to `X' ⊕ Unit`. There the shift vanishes, as the two string maps
  -- only move vectors of the strings.
  have h_vanish : (stackedStringMap Y Y' Y'').map Prod.snd *
      inclMatrix (𝔸f E) (Y'.indexEquiv ∘ Sum.inl) = 0 := by
    simp [mul_inclMatrix, ← Matrix.ext_iff, stackedStringMap, Y.formAdjoint_apply Y', stringMap,
      stringReversal, reindex_equiv Y.indexEquiv, reindex_equiv Y''.indexEquiv]
  have h_adjoint : (D.latticeLift hπ u κ)ᴴ =
      (D.neighbourLift hπ u κ)ᴴ ⊗ₖ (Y'.gradeZeroRowsᴴ)ᵀ := conjTranspose_kronecker _ _
  rw [h_adjoint, stackedStringMapFin, finCoord_homAtPoint, kronecker_mulVec_eq_matrixToVec,
    vecToMatrix_matrixToVec]
  simp [Matrix.mul_assoc, conjTranspose_gradeZeroRows, h_vanish]

/-- Let `P` contain one place of each conjugate pair above `N` (`hP`), let `N = π π̄`
with `π` a uniformiser at the places of `P` and a unit elsewhere (`hπ`), and let `κ` be scaling
factors with values `1` or `δ`, trivial above `N`, with denominators bounded by the integral adele
`β` and its conjugate (`hκ`).
Let `D` be the data of two consecutive lifts between the graded hermitian spaces `V`, `V'`,
`V''`, and let `V⁻` be `V` with the form negated.
For a unitary adele `u`, let `B = latticeLift` be the matrix of `x ↦ A x R`, where the columns
of `A` are the lifts to `V⁻ ⊕ V''` (`liftVector` for `u` and `κ`) of the columns of
`neighbourUnitary` and `R` consists of the rows of the point of `V'` at `X' ⊕ Unit`.
Let `g = latticeUnitary` be the unitary `(κ γ) ⊗ 1`, with `γ = neighbourUnitary` and `κ` read as a
diagonal matrix. Then `B x` is the image of `g x` in `Hom (V', V⁻ ⊕ V'')` (by `iFin`) plus a vector
of the isotropic subspace `I` of the splitting of `D`. Its coordinates in the basis
`isotropicBasisFin` of `I` are `isotropicCoeff` applied to `x`: zero in positive grade and
`planeCoeff ⊗ 1` at the hyperbolic planes, which `q` indexes. So `B x` lies in `I^⊥` and has the
class `g x` in `I^⊥ / I`. -/
lemma latticeLift_eq_latticeUnitary_add_isotropic (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ) :
    D.latticeLift hπ u κ =
      D.splitting.iFin * (latticeUnitary (X' ⊕ Unit) hπ hκ).val.val +
        D.splitting.isotropicBasisFin * isotropicCoeff q Y Y' Y'' P π u := by
  let f : E →+* 𝔸f E := algebraMap E (𝔸f E)
  let Z : Space E (PairIndex X X'') (-1 ⊕ᵥ 1) :=
    flipSum (stdSpace E (X ⊕ Unit)) (stdSpace E (X'' ⊕ Unit))
  let S : (hyperbolicSum q Z).Splitting Z q := removePlanes q Z
  -- In the part of grade zero, a lifted column is the column of `κ γ` in
  -- `(X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit)`, with `γ = neighbourUnitary`, plus an isotropic vector of the
  -- planes.
  let M : Matrix ((q ⊕ q) ⊕ PairIndex X X'') (PairIndex X X'') (𝔸f E) :=
    S.i.map f * (Z.xFin.val * (diagonal κ * (neighbourUnitary X X'' hπ : Matrix _ _ (𝔸f E)))) +
      S.k.map f * planeCoeff q P π u
  let A : Matrix (ι ⊕ ι'') ((q ⊕ q) ⊕ PairIndex X X'') (𝔸f E) :=
    (flipSum V V'').xFin⁻¹.val * D.zeroPart.incl.map f
  have h_neighbourLift_eq : D.neighbourLift hπ u κ = A * M := by
    ext1 i j
    have h_column : M.col j =
        ((0 : q → 𝔸f E) ⊕ᵥ fun _ : q ↦ (flipScale E : 𝔸f E) * u * neighbourCoeff X X'' P π j) ⊕ᵥ
          ((fun _ : X ⊕ Unit ↦ (flipScale E : 𝔸f E)) ⊕ᵥ (1 : X'' ⊕ Unit → 𝔸f E)) * κ *
            (neighbourUnitary X X'' hπ : Matrix _ _ (𝔸f E)).col j := by
      simp [funext_iff, Matrix.mul_apply, planeCoeff, M, S, Z, removePlanes, flipScale, xFin,
        Space.sum, flipSpace, ← mul_assoc, diagonal_apply, Matrix.one_apply, fromRows_map,
        fromBlocks_map]
    rw [neighbourLift, transpose_apply, of_apply, liftVector, ← h_column, mulVec_mulVec]
    rfl
  -- The image of `κ γ ⊗ 1` and that of `planeCoeff ⊗ 1` are Kronecker products with the same
  -- second factor, and their first factors add up to that of `latticeLift`.
  let R : Matrix ι' (X' ⊕ Unit) (𝔸f E) :=
    V'.xFin.valᵀ * inclMatrix (𝔸f E) (Y'.indexEquiv ∘ Sum.inl)
  obtain ⟨h_iFin, h_isotropic⟩ : D.splitting.iFin = (A * (S.i.map f * Z.xFin.val)) ⊗ₖ R ∧
      D.splitting.isotropicBasisFin * isotropicCoeff (X'' := X'') q Y Y' Y'' P π u =
        (A * (S.k.map f * planeCoeff q P π u)) ⊗ₖ R := by
    constructor <;>
      simp [A, R, S, Z, f, iFin, iAdelic, isotropicBasisFin, kAdelic, isotropicCoeff, Space.ratMap,
        splitting, Splitting.comp, homTarget, Space.hom, GradeZeroPart.splitting, homZeroPart,
        GradeZeroPart.hom, ← RingHom.coe_snd, ← RingHom.coe_comp, inclMatrix, xFin, toAdele,
        ← map_inv, ← submatrix_map, Matrix.mul_assoc, map_kronecker, fromCols_map,
        fromCols_mul_fromRows, ← mul_kronecker_mul, transpose_map]
  rw [coe_latticeUnitary hP, latticeLift, h_neighbourLift_eq, h_iFin, h_isotropic, gradeZeroRows,
    transpose_mul, transpose_transpose]
  simp [M, R, Matrix.mul_add, Matrix.mul_assoc, add_kronecker, ← mul_kronecker_mul]

omit [Fintype X'] in
/-- Let `P` contain one place of each conjugate pair above `N`, let `π` be the matching idele and
`κ` scaling factors with values `1` or `δ`. Suppose that the point of `V'` spans the lattice of
its grading `Y'` and that all neighbour vectors lift to the lattice of `V⁻ ⊕ V''`. Then the matrix
`B = latticeLift` of the pair of edges `D : Y → Y' → Y''` is integral:
its columns lie in the lattice `L` of the vacuum of `Hom (V', V⁻ ⊕ V'')`. -/
lemma isIntMatrix_latticeLift
    [Finite X'] (hP : IsSplitLevel P N) (hπ : IsSplitSquarefree P (N : E) π)
    (hκ : IsScalingAtM N β δ κ) {u' : unitary (𝔸f E)} (hL : Y'.SpansLattice a π u')
    (h_lift : D.LiftsNeighbours π u κ δ) : IsIntMatrix (Ô E) (D.latticeLift hπ u κ) := by
  intro i j
  have h_entry : D.neighbourLift hπ u κ i.1 j.1 ∈ Ô E :=
    h_lift _ _ (isNeighbourVector_col_neighbourUnitary hP hπ hκ j.1) i.1
  rw [latticeLift, kroneckerMap_apply, transpose_apply]
  exact mul_mem h_entry
    (Y'.isIntMatrix_gradeZeroRows hL (Nat.not_odd_iff_even.2 D.even_length_middle) j.2 i.2)

section DenominatorMatching

omit [Fintype X']

/-- Let `D` be the data of two consecutive lifts between `V`, `V'`, `V''`, let the place `w` and its
conjugate `star w` lie outside `P`, and let `j` be an index of
`PairIndex X X'' = (X ⊕ Unit) ⊕ (X'' ⊕ Unit)`. Suppose that the entry `(l, j)` of the inclusion of
`(X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit)` in `V⁻ ⊕ V''` is zero. Then, for all `u` and `κ`, the lift of the
column `j` of `neighbourUnitary`, with its coefficient `neighbourCoeff` at the isotropic vectors,
has entry `l` vanishing at `star w`. -/
lemma evalAt_liftVector_eq_zero (hπ : IsSplitSquarefree P (N : E) π) {j : PairIndex X X''}
    {w : FinPlace E} (hw_star : star w ∉ P) (hw_star_star : star (star w) ∉ P) {l : ι ⊕ ι''}
    (hl : D.zeroPart.incl l (Sum.inr j) = 0) :
    evalAt (star w) (D.liftVector u κ (neighbourCoeff X X'' P π j)
      ((neighbourUnitary X X'' hπ : Matrix _ _ (𝔸f E)).col j) l) = 0 := by
  -- At `star w` the column `j` of `neighbourUnitary` is the basis vector `j` and its coefficient
  -- is `0`, so only the column `j` of the inclusion counts.
  rw [liftVector, mulVec, dotProduct, map_sum]
  refine sum_eq_zero fun b _ ↦ ?_
  rw [map_mul]
  rcases b with (b | b) | b
  · simp
  · simp only [Sum.elim_inl, Sum.elim_inr, map_mul,
      neighbourCoeff_apply_of_notMem hw_star hw_star_star, mul_zero]
  · obtain rfl | hb := eq_or_ne b j
    · simp [hl]
    · simp only [Sum.elim_inr, Pi.mul_apply, map_mul, col_apply,
        evalAt_neighbourUnitary_of_notMem hπ hw_star hw_star_star, Matrix.one_apply,
        ite_eq_right hb, mul_zero]

/-- Let `P` contain one place of each conjugate pair above `N` (`hP`), and let `κ` be scaling
factors with values `1` or `δ`, trivial above `N`, with denominators bounded by the integral adele
`β` and its conjugate (`hκ`). Write `d = selfOrConj β`, which is `β` on the first block of indices
and `β̄` on the second. Suppose that `d l` and `d b * κ b` have the same valuation `v` at every
finite place whenever the entry `(l, b)` of the inclusion of `(X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit)` in
`V⁻ ⊕ V''` is nonzero (`h_match`). If `d i` and `d j * κ j` have different valuations at `w`, then,
for every unitary adele `u`, the entry `(i, j)` of `neighbourLift`, the matrix of the lifted
columns of `neighbourUnitary`, vanishes at the conjugate place `star w`. -/
lemma evalAt_neighbourLift_eq_zero (hP : IsSplitLevel P N) (hπ : IsSplitSquarefree P (N : E) π)
    (hκ : IsScalingAtM N β δ κ) (h_match : D.MatchesDenominators κ β) {i : ι ⊕ ι''}
    {j : PairIndex X X''} {w : FinPlace E}
    (h_ne : v (selfOrConj β i w) ≠ v ((selfOrConj β j * κ j) w)) :
    evalAt (star w) (D.neighbourLift hπ u κ i j) = 0 := by
  -- Above `N` all denominators are units, so `w` is not above `N`.
  have hw : ¬(w ∈ P ∨ star w ∈ P) := by
    rw [← hP.natCast_mem_iff]
    intro hN
    have h_κ : κ j w = 1 := by
      rcases hκ.eq_one_or_eq j with h_val | h_val <;> simp [h_val, hκ.apply_eq_one w hN]
    exact h_ne (by simp [v_selfOrConj_eq_one hκ _ hN, h_κ])
  obtain ⟨hw_P, hw_star⟩ := not_or.1 hw
  rw [neighbourLift, transpose_apply, of_apply, mulVec, dotProduct, map_sum]
  refine sum_eq_zero fun l _ ↦ ?_
  by_cases hl : D.zeroPart.incl l (Sum.inr j) = 0
  · rw [map_mul, D.evalAt_liftVector_eq_zero hπ hw_star (by rwa [star_star]) hl, mul_zero]
  · -- Here `i` and `l` lie in different blocks, and the point of `V⁻ ⊕ V''` is block diagonal.
    have h_val : v (selfOrConj β l w) = v ((selfOrConj β j * κ j) w) := h_match l j hl w
    rw [inv_xFin_flipSum]
    rcases i with i | i <;> rcases l with l | l <;>
      first | exact h_ne.elim h_val | simp

/-- Let `P` contain one place of each conjugate pair above `N` (`hP`) and let `κ` be scaling factors
with values `1` or `δ`, trivial above `N` (`hκ`). Let `D` be double-lift data for `Y`, `Y'`, `Y''`
whose matrix `B = D.latticeLift hπ u κ` is integral (`h_int`) and whose denominators match through
`κ` (`h_match`). Then `Bᴴ` keeps the allowed denominators up to `κ`: if each entry of `y` in a row
`(i, i')`, times `selfOrConj β i`, is integral at the places not dividing `n`, then so is each entry
of `Bᴴ y` in a row `(j, j')`, times `selfOrConj β j * κ j`. -/
lemma conjTranspose_latticeLift_mulVec_mem (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ)
    (h_match : D.MatchesDenominators κ β) (h_int : IsIntMatrix (Ô E) (D.latticeLift hπ u κ))
    {n : ℕ} {y : (ι ⊕ ι'') × ι' → 𝔸f E}
    (hy : y ∈ weightedTranslations n fun i : (ι ⊕ ι'') × ι' ↦ selfOrConj β i.1) :
    (D.latticeLift hπ u κ)ᴴ *ᵥ y ∈ weightedTranslations n
      fun j : PairIndex X X'' × (X' ⊕ Unit) ↦ selfOrConj β j.1 * κ j.1 := by
  exact conjTranspose_mulVec_mem_weightedTranslations h_int hy fun i j w h_ne ↦
    mul_eq_zero_of_left (D.evalAt_neighbourLift_eq_zero hP hπ hκ h_match h_ne) _

end DenominatorMatching

end DoubleLiftData

/-- Let `P` contain one place of each conjugate pair above the prime `N` (`hP`), let `N = π π̄`
with `π` a uniformiser at the places of `P` and a unit elsewhere (`hπ`), and let `κ` be scaling
factors with values `1` or `δ`, trivial above `N`, with denominators bounded by the integral adele
`β` and its conjugate (`hκ`).
Let `D` be the data of two consecutive lifts between the graded hermitian spaces `V`, `V'`, `V''`,
with hyperbolic planes indexed by `q`, and let `V⁻` be `V` with the form negated. Suppose that the
point of `V'` spans the lattice of `gradedLatticeBasis` for `a`, `π`, `u'`, that the solutions of
the congruences `IsNeighbourVector` lift to the lattice of `V⁻ ⊕ V''`, and that the denominators
match through `κ`. The map `D.finEval` translates by `stackedStringMapFin`, takes the finite
constant term along the splitting of `D` and splits the result into a tensor. There is then a
constant `C` such that, for `n` prime to `N` and `y` with denominators `β` on `V⁻` and `β̄` on
`V''` away from `n`, it sends the vacuum translated by `y` to a finite combination of vectors
`C • gluedTranslate N P (t₁, t₂)` (the gluing of the tensor of the vacua translated by `t₁`, `t₂`)
with `β̄ t₁`, `β̄ t₂` integral away from `n`. The coefficients have a denominator away from `n`
that depends only on `β` and the index types, and absolute sum at most `1` under every automorphism
of `ℂ` (`IsAdmissibleEval`). -/
theorem isAdmissibleEval_finEval {Y'' : Grading V'' N μ m''} [Fact N.Prime]
    {P : Finset (FinPlace E)} {a π : (𝔸f E)ˣ} {u u' : unitary (𝔸f E)} {β : Ô E} {δ : 𝔸f E}
    {κ : PairIndex X X'' → 𝔸f E}
    (D : DoubleLiftData (X'' ⊕ Unit) q Y Y' Y'') (hP : IsSplitLevel P N)
    (hπ : IsSplitSquarefree P (N : E) π) (hκ : IsScalingAtM N β δ κ)
    (hL : Y'.SpansLattice a π u') (h_lift : D.LiftsNeighbours π u κ δ)
    (h_match : D.MatchesDenominators κ β) :
    IsAdmissibleEval N P β D.finEval (selfOrConj β) := by
  classical
  let W := V'.hom (flipSum V V'')
  let Z := stdPairSpace E X (X' ⊕ Unit) X''
  let B := D.latticeLift hπ u κ
  let g_N : Gf E (PairIndex X X'' × (X' ⊕ Unit)) :=
    kroneckerOne (X' ⊕ Unit) (PairIndex X X'') (neighbourUnitary X X'' hπ)
  let g_M : Gf E (PairIndex X X'' × (X' ⊕ Unit)) :=
    kroneckerOne (X' ⊕ Unit) (PairIndex X X'') (scalingUnitary hκ)
  let S : Set (FinPlace E) := star ⁻¹' (P : Set (FinPlace E))
  have hB_int : IsIntMatrix (Ô E) B := D.isIntMatrix_latticeLift hP hπ hκ hL h_lift
  -- Step 1: `zeroTermFin D.splitting` sends any translate `W.finHeisenbergOp z W.vacElem` to `0`
  -- or a root of unity times `C₀ • Z.ω (1, g_N * g_M) (Z.finHeisenbergOp (Bᴴ *ᵥ z) Z.vacElem)`.
  obtain ⟨C₀, hC₀⟩ := exists_zeroTermFin_finHeisenbergOp_vacElem
    (D.latticeLift_eq_latticeUnitary_add_isotropic hP hπ hκ (u := u)) hB_int
  let C_M : ℂ := finMultiplier g_M
  let C_N : ℂ := starRingEnd ℂ (chiAdelic (detOn S g_N.val))
  let d_card : ℕ := Nat.card (PairIndex X X'' × (X' ⊕ Unit) → Ô E ⧸ Ideal.span {β})
  refine ⟨C₀ * C_M * C_N, fun n p hn y hy ↦ ?_⟩
  let τ : (ι ⊕ ι'') × ι' → 𝔸f E := stackedStringMapFin Y Y' Y''
  let ξ : ℂ := selfDualAddChar E (star traceOneAdele * star y ⬝ᵥ τ)
  obtain ⟨ζ₀, hζ₀, h_zeroTerm⟩ := hC₀ (τ + y)
  have hB_shift : Bᴴ *ᵥ (τ + y) = Bᴴ *ᵥ y := by
    rw [mulVec_add, D.conjTranspose_latticeLift_mulVec_stackedStringMapFin, zero_add]
  have h_eval : D.finEval (W.finHeisenbergOp y W.vacElem) =
      (ξ * ζ₀) • arrowTensor.leftInverse
        (C₀ • Z.ω (1, g_N) (Z.ω (1, g_M) (Z.finHeisenbergOp (Bᴴ *ᵥ y) Z.vacElem))) := by
    change arrowTensor.leftInverse
      (zeroTermFin D.splitting (W.finHeisenbergOp τ (W.finHeisenbergOp y W.vacElem))) = _
    have hg_mul : latticeUnitary (X' ⊕ Unit) hπ hκ = g_N * g_M := map_mul _ _ _
    rw [finHeisenbergOp_finHeisenbergOp, map_smul, h_zeroTerm, hB_shift, hg_mul,
      show ((1 : GInf E _), g_N * g_M) = (1, g_N) * (1, g_M) by simp, Z.ω.map_mul,
      mul_apply_eq_comp]
    simp only [map_smul, smul_smul, mul_assoc]
    rfl
  rw [h_eval]
  refine IsAdmissibleCombination.smul_of_eq_zero_or_isOfFinOrder ?_
    (hζ₀.imp (fun h ↦ by simp [h]) (isOfFinOrder_ψf _).mul)
  -- Step 2: Away from `N`, `Z.ω (1, g_M)` scales rows by `κ`, turning `Bᴴ *ᵥ y` into an
  -- admissible combination of translates with denominators `selfOrConj β` away from `n`.
  have hx_den : Bᴴ *ᵥ y ∈ weightedTranslations n
      fun j : PairIndex X X'' × (X' ⊕ Unit) ↦ selfOrConj β j.1 * κ j.1 :=
    D.conjTranspose_latticeLift_mulVec_mem hP hπ hκ h_match hB_int hy
  have h_scaled_mem (z : PairIndex X X'' × (X' ⊕ Unit) → 𝔸f E)
      (hz : z ∈ stdLattice E (PairIndex X X'' × (X' ⊕ Unit))) :
      (g_M : Matrix _ _ (𝔸f E)) *ᵥ (Bᴴ *ᵥ y + z) ∈
        weightedTranslations n fun j : PairIndex X X'' × (X' ⊕ Unit) ↦ selfOrConj β j.1 := by
    have h_smul : (g_M : Matrix _ _ (𝔸f E)) *ᵥ (Bᴴ *ᵥ y + z) =
        fun j ↦ κ j.1 * (Bᴴ *ᵥ y) j + κ j.1 * z j := by
      ext1 j
      change (g_M • (Bᴴ *ᵥ y + z)) j = _
      simpa [g_M, mul_add] using kroneckerOne_scalingUnitary_smul hκ (Bᴴ *ᵥ y + z) j
    rw [h_smul]
    refine add_mem (fun j w' hw' ↦ ?_) fun j w' _ ↦ ?_
    · simpa [← mul_assoc] using hx_den j w' hw'
    · rw [← mul_assoc]
      exact mem_Ô.1 (mul_mem (hκ.selfOrConj_mul_mem j.1) (hz j)) w'
  have h_mult_int : (d_card : ℂ) * (1 / (‖finMultiplier g_M‖ : ℂ) ^ 2) ∈ integralAway n := by
    let L := stdLattice E (PairIndex X X'' × (X' ⊕ Unit))
    let H : AddSubgroup L :=
      (L.comap (g_M : Matrix _ _ (𝔸f E)).mulVecLin.toAddMonoidHom).addSubgroupOf L
    have h_norm : (‖finMultiplier g_M‖ : ℂ) ^ 2 = (H.index : ℂ) := by
      exact_mod_cast norm_finMultiplier_sq g_M
    rw [h_norm]
    simpa [div_eq_mul_inv] using
      div_mem_integralAway ((index_scalingUnitary_dvd (X' := X' ⊕ Unit) hκ).mul_right (n ^ 0))
  have h_comb_M : IsAdmissibleCombination (fun w ↦ C_M • Z.finHeisenbergOp w Z.vacElem)
      (weightedTranslations n fun j : PairIndex X X'' × (X' ⊕ Unit) ↦ selfOrConj β j.1) n
      d_card p 1 (Z.ω (1, g_M) (Z.finHeisenbergOp (Bᴴ *ᵥ y) Z.vacElem)) :=
    isAdmissibleCombination_weil_vacElem Z (one_mul C_M) h_scaled_mem h_mult_int (by simp)
  -- Step 3: Above `N`, apply `arrowTensor.leftInverse ∘ (C₀ • Z.ω (1, g_N))`; on each `w`,
  -- `omega_neighbourUnitary_finHeisenbergOp_vacElem` yields a root of unity times `gluedTranslate`.
  let T := arrowTensor.leftInverse ∘ₗ (C₀ • Z.ω (1, g_N)).toLinearMap
  refine (h_comb_M.map T).of_eq_isOfFinOrder_smul fun w hw ↦ ?_
  obtain ⟨ζ_w, hζ_w, t₁, ht₁, t₂, ht₂, h_glue⟩ :=
    exists_sum_finHeisenbergOp_neighbourTranslation_eq hπ hw
  refine ⟨ζ_w, hζ_w, (t₁, t₂), ⟨ht₁, ht₂⟩, ?_⟩
  have h_omega_N : Z.ω (1, g_N) (Z.finHeisenbergOp w Z.vacElem) =
      C_N • ζ_w • arrowTensor (gluedTranslate N P (t₁, t₂)) := by
    rw [omega_neighbourUnitary_finHeisenbergOp_vacElem hP hπ hκ hn hw, h_glue]
  change arrowTensor.leftInverse (C₀ • Z.ω (1, g_N) (C_M • Z.finHeisenbergOp w Z.vacElem)) = _
  simp only [map_smul, h_omega_N, leftInverse_arrowTensor, smul_smul]
  congr 1
  ring

end Lift

/-! ### Verification for `middleDoubleLift` and `lastDoubleLift` -/

section Pairs

variable {ι ι' ι'' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype ι''] [DecidableEq ι''] {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {ε'' : ι'' → ℤˣ}

/-- Let `Y`, `Y'`, `Y''` present the hermitian spaces `V`, `V'`, `V''` as orthonormal vectors
`X ⊕ Unit`, `X' ⊕ Unit`, `X'' ⊕ Unit` plus strings of `m`, `m - 1`, `m - 2` further basis vectors,
paired in reverse order, with `m` odd and `Y.genericConst = Y'.genericConst` (`h_string`). Let
`m ≠ 1` and let `dim V + dim V''` be even. The middle vectors `z`, `z''` of the strings of `V`,
`V''` have norm `-N`, so `z + z''` is isotropic in `V⁻ ⊕ V''`. Suppose that the points (adelic bases
`xFin`) of `V` and `V''` span the lattices of `gradedLatticeBasis` for `a`, `π` and `u`, `u''`, and
that `s u = η̄ δ u''`, where `η = normNegOne` has `η̄ η = -1` and `s = flipScale E` scales the point
of `V⁻`. Let `e`, `e''` be the last indices of `X ⊕ Unit`, `X'' ⊕ Unit`, and let `(c, x)` satisfy
`IsNeighbourVector π δ c x`: `δ c = c`, the entries of `x` are integral except that `x e`, `x e''`
have denominator at most `π̄`, and `x e / π ≡ c`, `x e'' / π ≡ η̄ c` modulo integral adeles. Then
the lift of `(c, x)`, with component `s x` in `X ⊕ Unit`, `x` in `X'' ⊕ Unit` and coefficient
`s u c` at `z + z''`, lies in the lattice of `V⁻ ⊕ V''`. -/
lemma liftsNeighbours_middleDoubleLift {V : Space E ι ε} {V' : Space E ι' ε'}
    {V'' : Space E ι'' ε''} {N m m' m'' : ℕ} {Y : Grading V N (X ⊕ Unit) m}
    {Y' : Grading V' N (X' ⊕ Unit) m'} {Y'' : Grading V'' N (X'' ⊕ Unit) m''}
    (h_string : HasConsecutiveStrings Y Y' Y'')
    (h_card : Even (Fintype.card ι + Fintype.card ι'')) (hm : m ≠ 1)
    {a π : (𝔸f E)ˣ} {u u'' : unitary (𝔸f E)} {δ : 𝔸f E}
    (hL : Y.SpansLattice a π u) (hL'' : Y''.SpansLattice a π u'')
    (h_scale : (flipScale E : 𝔸f E) * u = star (normNegOne (E := E) : 𝔸f E) * δ * u'') :
    (middleDoubleLift Y Y' Y'' h_string h_card hm).LiftsNeighbours π u 1 δ := by
  intro c x hx
  have h_odd : Odd m := h_string.odd_length
  have h_odd'' : Odd m'' := by grind [h_string.length_last, h_string.length_middle]
  -- The entries of the lift `y`: those of `x`, scaled by `s = flipScale E` in `X ⊕ Unit`, and
  -- `s u c` at the middle vectors `z` and `z''`.
  set y : ι ⊕ ι'' → 𝔸f E := (middleDoubleLift Y Y' Y'' h_string h_card hm).liftVector u 1 c x with
    hy
  have h_middle {k : ℕ} (hk : Odd k) (b : Fin k) : b.val = k / 2 ↔ 2 * b.val + 1 = k := by grind
  obtain ⟨hy_source, hy_string, hy_target, hy_string''⟩ :
      (∀ i : X ⊕ Unit, y (Sum.inl (Y.indexEquiv (Sum.inl i))) = flipScale E * x (Sum.inl i)) ∧
      (∀ b : Fin m, y (Sum.inl (Y.indexEquiv (Sum.inr b))) =
        if 2 * b.val + 1 = m then (flipScale E : 𝔸f E) * u * c else 0) ∧
      (∀ i : X'' ⊕ Unit, y (Sum.inr (Y''.indexEquiv (Sum.inl i))) = x (Sum.inr i)) ∧
      ∀ b : Fin m'', y (Sum.inr (Y''.indexEquiv (Sum.inr b))) =
        if 2 * b.val + 1 = m'' then (flipScale E : 𝔸f E) * u * c else 0 := by
    simp [hy, liftVector, middleDoubleLift, inclMatrix, Matrix.one_apply, mulVec, dotProduct,
      Fin.ext_iff, h_middle h_odd, h_middle h_odd'']
  refine (inv_xFin_flipSum_mulVec_mem_iff V V'' y).2 ⟨?_, ?_⟩
  · -- In `V`, after division by `s`, the entries are those of `x`, and `u c` at `z`.
    refine inv_xFin_mulVec_mem_of_spansLattice hL h_odd (x := x ∘ Sum.inl)
      (fun i : X ↦ hx.mem_of_ne _ (by simp) (by simp))
      (hx.star_mul_mem lastSource) hx.sub_source_mem (fun i ↦ ?_) fun b ↦ ?_
    · simp [hy_source]
    · simp [hy_string, mul_assoc]
  · -- In `V''` the coefficient at `z''` is `u'' η̄ δ c = u'' η̄ c`, with `η = normNegOne`.
    have h_coeff : (flipScale E : 𝔸f E) * u * c =
        u'' * (star (normNegOne (E := E) : 𝔸f E) * c) := by
      linear_combination c * h_scale + star (normNegOne (E := E) : 𝔸f E) * u'' * hx.mul_coeff
    refine inv_xFin_mulVec_mem_of_spansLattice hL'' h_odd'' (x := x ∘ Sum.inr)
      (fun i : X'' ↦ hx.mem_of_ne _ (by simp) (by simp))
      (hx.star_mul_mem lastTarget) hx.sub_target_mem hy_target fun b ↦ ?_
    simp [hy_string'', h_coeff]

/-- In a middle pair (strings of lengths `m`, `m - 1`, `m - 2` with `m` odd and not `1`) the
inclusion of `(X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit)` in `V⁻ ⊕ V''` keeps each index in its block, so the
denominators `β` on the first block and `β̄` on the second match without any scaling. -/
lemma matchesDenominators_middleDoubleLift {V : Space E ι ε} {V' : Space E ι' ε'}
    {V'' : Space E ι'' ε''} {N m m' m'' : ℕ} {Y : Grading V N (X ⊕ Unit) m}
    {Y' : Grading V' N (X' ⊕ Unit) m'} {Y'' : Grading V'' N (X'' ⊕ Unit) m''}
    (h_string : HasConsecutiveStrings Y Y' Y'')
    (h_card : Even (Fintype.card ι + Fintype.card ι'')) (hm : m ≠ 1) {β : Ô E} :
    (middleDoubleLift Y Y' Y'' h_string h_card hm).MatchesDenominators 1 β := by
  rintro (i | i) (b | b) h_ne w <;>
    simp_all [middleDoubleLift, selfOrConj, inclMatrix, Matrix.one_apply]

variable (X X'') in
/-- The scaling of the last pair: `δ` at the last basis vector of `X'' ⊕ Unit` and `1`
elsewhere. -/
def lastScaling (δ : 𝔸f E) : PairIndex X X'' → 𝔸f E := 1 ⊕ᵥ (1 ⊕ᵥ fun _ ↦ δ)

/-- Let `Y`, `Y'`, `Y''` present the hermitian spaces `V`, `V'`, `V''` as orthonormal vectors
`X ⊕ Unit`, `X' ⊕ Unit`, `X''` plus strings of `1`, `0`, `0` further basis vectors, with
`Y.genericConst = Y'.genericConst` (`h_string`, `hm`). Let `V''` be standard, `dim V + dim V''` even
and `N = p p̄`. The string vector `z` of `V` has norm `-N`, so `z / p` has norm one in `V⁻`, which
is `V` with the form negated; `lastDoubleLift` identifies `V⁻ ⊕ V''` with
`(X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit)`. Suppose that `π` is the principal idele of `p`, that the point (adelic
basis `xFin`) of `V` spans the lattice of `gradedLatticeBasis` for `a`, `π`, `u`, and that
`s u = η̄ δ`, where `η = normNegOne` has `η̄ η = -1` and `s = flipScale E` scales the point of `V⁻`.
Let `e`, `e''` be the last indices of `X ⊕ Unit`, `X'' ⊕ Unit`, and let `(c, x)` satisfy
`IsNeighbourVector π δ c x`: `δ c = c`, the entries of `x` are integral except that `x e`, `x e''`
have denominator at most `π̄`, and `x e / π ≡ c`, `x e'' / π ≡ η̄ c` modulo integral adeles. Then
the lift of `(c, x)`, with component `s x` in `X ⊕ Unit`, `x` in `X''` and coefficient `δ x e'' / p`
at `z`, lies in the lattice of `V⁻ ⊕ V''`; there is no hyperbolic plane, so `u c` does not enter the
lift. -/
lemma liftsNeighbours_lastDoubleLift {V : Space E ι ε} {V' : Space E ι' ε'}
    {V'' : Space E ι'' ε''} {N m m' m'' : ℕ} {Y : Grading V N (X ⊕ Unit) m}
    {Y' : Grading V' N (X' ⊕ Unit) m'} [V''.IsStd] {Y'' : Grading V'' N X'' m''}
    (h_string : HasConsecutiveStrings Y Y' Y'')
    (h_card : Even (Fintype.card ι + Fintype.card ι'')) {p : E} (hp : p * star p = N) (hm : m = 1)
    {a π : (𝔸f E)ˣ} {u : unitary (𝔸f E)} {δ : 𝔸f E}
    (hπ : (↑π⁻¹ : 𝔸f E) = algebraMap E (𝔸f E) p⁻¹) (hL : Y.SpansLattice a π u)
    (h_scale : (flipScale E : 𝔸f E) * u = star (normNegOne (E := E) : 𝔸f E) * δ) :
    (lastDoubleLift Y Y' Y'' h_string h_card hp hm).LiftsNeighbours π u (lastScaling X X'' δ)
      δ := by
  intro c x hx
  -- The entries of the lift `y`: those of `x`, scaled by `s = flipScale E` in `X ⊕ Unit`, and
  -- `p⁻¹ δ x e''` at the string vector `z`.
  set y : ι ⊕ ι'' → 𝔸f E :=
    (lastDoubleLift Y Y' Y'' h_string h_card hp hm).liftVector u (lastScaling X X'' δ) c x with hy
  obtain ⟨hy_source, hy_string, hy_target⟩ :
      (∀ i : X ⊕ Unit, y (Sum.inl (Y.indexEquiv (Sum.inl i))) = flipScale E * x (Sum.inl i)) ∧
      (∀ b : Fin m, y (Sum.inl (Y.indexEquiv (Sum.inr b))) = ↑π⁻¹ * (δ * x lastTarget)) ∧
      ∀ i : X'', y (Sum.inr (Y''.indexEquiv (Sum.inl i))) = x (Sum.inr (Sum.inl i)) := by
    subst hm
    simp [hy, liftVector, lastDoubleLift, lastScaling, mulVec, dotProduct, univ_eq_empty, ← hπ,
      Fin.forall_fin_one]
  refine (inv_xFin_flipSum_mulVec_mem_iff V V'' y).2 ⟨?_, ?_⟩
  · -- Add `η = normNegOne` times the congruence at `e''` to the congruence at the last basis vector
    -- `e` of `X ⊕ Unit`. As `η̄ η = -1`, the terms in `c` cancel.
    let η : 𝔸f E := normNegOne (E := E)
    have h_congr : -(↑π⁻¹ * x lastSource) - η * (↑π⁻¹ * x lastTarget) ∈ Ô E := by
      rw [show -(↑π⁻¹ * x lastSource) - η * (↑π⁻¹ * x lastTarget) =
          (c - ↑π⁻¹ * x lastSource) + η * (star η * c - ↑π⁻¹ * x lastTarget) by
        linear_combination -c * star_normNegOne_mul_self (E := E)]
      exact add_mem hx.sub_source_mem (mul_mem normNegOne_mem hx.sub_target_mem)
    refine inv_xFin_mulVec_mem_of_spansLattice hL h_string.odd_length (x := x ∘ Sum.inl)
      (fun i : X ↦ hx.mem_of_ne _ (by simp) (by simp))
      (hx.star_mul_mem lastSource) h_congr (fun i ↦ ?_) fun b ↦ ?_
    · simp [hy_source]
    · -- The coordinate at `z` is `s⁻¹ p⁻¹ δ x e''`, and `s⁻¹ δ = -η u`.
      have h_δ : (↑(flipScale E)⁻¹ : 𝔸f E) * δ = -(η * u) := by
        rw [Units.inv_mul_eq_iff_eq_mul]
        linear_combination η * h_scale + δ * star_normNegOne_mul_self (E := E)
      have h_coord : (↑(flipScale E)⁻¹ : 𝔸f E) * (↑π⁻¹ * (δ * x lastTarget)) =
          u * (↑π⁻¹ * x lastSource + (-(↑π⁻¹ * x lastSource) - η * (↑π⁻¹ * x lastTarget))) := by
        linear_combination ↑π⁻¹ * x lastTarget * h_δ
      simpa [hy_string, show 2 * b.val + 1 = m by lia] using h_coord
  · -- The point of `V''` is the identity and its string is empty, so the coordinates are entries
    -- of `x` other than those at `e` and `e''`.
    have h_point : V''.xFin = 1 := by simp [xFin, IsStd.point_eq_one]
    intro i
    obtain ⟨i | b, rfl⟩ := Y''.indexEquiv.surjective i
    · simpa [h_point, hy_target] using hx.mem_of_ne _ (by simp) (by simp)
    · exact (b.cast (by rw [h_string.length_last, h_string.length_middle, hm])).elim0

/-- Let `Y`, `Y'`, `Y''` present the hermitian spaces `V`, `V'`, `V''` as orthonormal vectors
`X ⊕ Unit`, `X' ⊕ Unit`, `X''` plus strings of `m = 1`, `m' = 0`, `m'' = 0` further basis vectors,
with `Y.genericConst = Y'.genericConst` (`h_string`, `hm`). Let `dim V + dim V''` be even and
`N = p p̄`. In `lastDoubleLift` the last basis vector `e''` of `X'' ⊕ Unit` is `z / p` for the
string vector `z` of `V⁻`. If, for the integral adele `β`, `β̄ δ` and `β` have the same valuation at
every finite place, then the denominators of indices joined by the inclusion of
`(X ⊕ Unit)⁻ ⊕ (X'' ⊕ Unit)` in `V⁻ ⊕ V''` have the same valuations after the scaling `lastScaling`,
which is `δ` at `e''` and `1` elsewhere. -/
lemma matchesDenominators_lastDoubleLift {V : Space E ι ε} {V' : Space E ι' ε'}
    {V'' : Space E ι'' ε''} {N m m' m'' : ℕ} {Y : Grading V N (X ⊕ Unit) m}
    {Y' : Grading V' N (X' ⊕ Unit) m'} {Y'' : Grading V'' N X'' m''}
    (h_string : HasConsecutiveStrings Y Y' Y'')
    (h_card : Even (Fintype.card ι + Fintype.card ι'')) {p : E} (hp : p * star p = N) (hm : m = 1)
    {β : Ô E} {δ : 𝔸f E} (hδ : ∀ w : FinPlace E, v ((star (β : 𝔸f E) * δ) w) = v ((β : 𝔸f E) w)) :
    (lastDoubleLift Y Y' Y'' h_string h_card hp hm).MatchesDenominators (lastScaling X X'' δ)
      β := by
  -- The only index that changes its block is the last one, whose denominator `β̄` is scaled by `δ`.
  rintro (i | i) (b | b | b) h_ne w
  · simp [lastScaling, selfOrConj]
  · simp [lastDoubleLift] at h_ne
  · simpa [lastScaling, selfOrConj] using (hδ w).symm
  · simp [lastDoubleLift] at h_ne
  · simp [lastScaling, selfOrConj]
  · simp [lastDoubleLift] at h_ne

end Pairs

end AdmissibleEvaluation

end New.Seesaw

end
