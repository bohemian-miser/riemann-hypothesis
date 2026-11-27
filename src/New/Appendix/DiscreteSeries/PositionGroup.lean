module

import Mathlib.Topology.Algebra.Group.Units
public import Lib.General.LinearAlgebra.BlockEmbeddings
public import New.Appendix.DiscreteSeries.Positions
import Lib.DiscreteSeries.FlenstedJensen.PsiKTypes
import Lib.DiscreteSeries.FlenstedJensen.RightDerivatives
import Lib.DiscreteSeries.Haar.GramPolar
import Lib.Shimura.ComplexTheta.AppellHumbertData
import New.Appendix.DiscreteSeries.Periods
import New.Appendix.DiscreteSeries.StationaryPosition

/-!
# Laplace data from a stationary position

In a stationary position `(v, i₀)` of `U(η)` in `U(ε)`, any homomorphism `j : S →* U(ε) × U(η)`
whose first component minus `1` lowers the flag of `v` with coefficient sum `σ`, acts on the image
of `i₀` modulo `A_{≤ j₀ - 1}` by the second component, and contains a diagonal copy of `U(X)` in
its image satisfies `IsLaplaceDatum` (`IsStationary.isLaplaceDatum`).

## Main definitions and results

* `IsStationary.exists_diagonal_of_exists_ext`: if the image of `j` lifts every `y ∈ U(η)` by
  `g - 1 = i₀ (y - 1) i₀†`, then it contains the diagonal copy of `U(X)`.
* `IsStationary.isLaplaceDatum`: a homomorphism `j : S →* U(ε) × U(η)` that lowers the flag of a
  stationary position, induces the second component on `i₀`, and contains the diagonal `U(X)` gives
  a Laplace datum with imaginary additive phase `σ - conj σ`.
* `IsSteep.exists_volume_le_mul_norm_integral_dsCoeff`: the pairing over `U(ε)` of a coefficient of
  `U(ε)` with a conjugated coefficient of `U(ε ⊕ 1)` is bounded below, via Laplace's method in a
  stationary position with one vector `v₁` and conjugation by `w = (i₀, v₁)`.

Notions from other files:
* `USign ε` is the unitary group `U(ε)` of the diagonal matrix `signMatrix ε` of signs, and
  `formAdjoint ε η A` is the adjoint `A†` of `A : (ℂ^m, η) → (ℂ^n, ε)` for these forms.
* `IsPosition ε η d v i₀`: the columns `v₁, …, v_{j₀}` of `v`, `j₀ = d + 1`, are independent, their
  products vanish except that `v_{j₀}` has norm `±1`, `i₀` is an isometry into their orthogonal
  complement, and `card n = card m + 2 d + 1`.
* `LowersFlag d v Y σ`: `Y` maps the span `A_{≤ j}` of `v₁, …, v_j` into `A_{≤ j - 1}` for `j ≤ j₀`,
  and `σ` is the sum of the coefficients of `v_j` in `Y v_{j + 1}`.
* `InducesOn d v i₀ Y Y'`: `Y i₀ = i₀ Y'` modulo `A_{≤ j₀ - 1}`.
* `IsSteep l B e`: for `e : X ⊕ Fin M ≃ n`, the weight of the lowest `K`-type of `l` is `0` on `X`
  and decreases in `[-3 B, -B]` on the other coordinates, with alternating signs there.
* `IsLaplaceDatum` collects the hypotheses of Laplace's method on a map into `U(ε) × U(η)`.
-/

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory ComplexConjugate Norms.L2Operator

namespace New.DiscreteSeries

variable {n m X : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] {ε : n → ℤˣ}
  {η : m → ℤˣ} {d : ℕ} {v : Matrix n (Fin (d + 1)) ℂ} {i₀ : Matrix n m ℂ}

/-- Let `(v, i₀)` be a stationary position for `l` and `k`, where `e` and `e'` place the common
coordinates `X` in `n` and `m`, so that `i₀` is the identity on `ℂ^X`. Assume that the signs `ε`
and `η` are `+1` on `X`. If for every `y` in `U(η)` there is an `s` in `S` with `(j s).2 = y` and
`(j s).1 - 1 = i₀ (y - 1) i₀†`, where `i₀† = formAdjoint ε η i₀`, then the image of `j` contains
the diagonal copy of `U(X)`. -/
lemma IsStationary.exists_diagonal_of_exists_ext [Fintype X] [DecidableEq X] {l : HCParam ε}
    {k : HCParam η} {M M' : ℕ} {e : X ⊕ Fin M ≃ n} {e' : X ⊕ Fin M' ≃ m}
    (hP : IsStationary l k e e' d v i₀)
    (h_sign_left : ∀ x : X, ε (e (Sum.inl x)) = 1)
    (h_sign_right : ∀ x : X, η (e' (Sum.inl x)) = 1)
    {S : Type} [Group S] {j : S →* USign ε × USign η}
    (h_ext : ∀ y : USign η, ∃ s : S, (j s).2 = y ∧
      (subOnePair j s).1 = i₀ * ((y : Matrix m m ℂ) - 1) * formAdjoint ε η i₀)
    (u : Matrix X X ℂ) (hu : u ∈ unitaryGroup X ℂ) :
    ∃ s : S, subOnePair j s =
      (inclMatrix ℂ (e ∘ Sum.inl) * (u - 1) * (inclMatrix ℂ (e ∘ Sum.inl))ᴴ,
        inclMatrix ℂ (e' ∘ Sum.inl) * (u - 1) * (inclMatrix ℂ (e' ∘ Sum.inl))ᴴ) := by
  -- Extend `u` by `1` on the complement of `X` in `m`, then lift it along `i₀`.
  obtain ⟨y, hy⟩ : ∃ y : USign η, (y : Matrix m m ℂ) - 1 =
      inclMatrix ℂ (e' ∘ Sum.inl) * (u - 1) * (inclMatrix ℂ (e' ∘ Sum.inl))ᴴ :=
    exists_unitary_sub_one_eq_inclMatrix e' h_sign_right (mem_unitaryGroup_iff'.1 hu)
  obtain ⟨s, hs_snd, hs_fst⟩ := h_ext y
  have h_inc : i₀ * inclMatrix ℂ (e' ∘ Sum.inl) = inclMatrix ℂ (e ∘ Sum.inl) := by
    rw [mul_inclMatrix]
    ext i x
    simp [inclMatrix, hP.apply_inl, Matrix.one_apply]
  have h_inc_adj : (inclMatrix ℂ (e' ∘ Sum.inl))ᴴ * formAdjoint ε η i₀ =
      (inclMatrix ℂ (e ∘ Sum.inl))ᴴ := by
    rw [← formAdjoint_inclMatrix (τ := e' ∘ Sum.inl) h_sign_right, ← formAdjoint_mul, h_inc,
      formAdjoint_inclMatrix (τ := e ∘ Sum.inl) h_sign_left]
  have h_snd : (subOnePair j s).2 =
      inclMatrix ℂ (e' ∘ Sum.inl) * (u - 1) * (inclMatrix ℂ (e' ∘ Sum.inl))ᴴ := by
    change ((j s).2 : Matrix m m ℂ) - 1 = _
    rw [hs_snd, hy]
  refine ⟨s, Prod.ext ?_ h_snd⟩
  rw [hs_fst, hy, Matrix.mul_assoc, Matrix.mul_assoc, h_inc_adj, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc, h_inc]

/-- Let `(v, i₀)` be a stationary position for the parameters `l` and `k`, where `e` and `e'` place
the common coordinates `X` in `n` and `m`, and let `l` be steep: on `X` its sign is `+1` and its
weight is `0`, and on the other coordinates the signs alternate and the weight decreases strictly in
`[-3 B, -B]`. On `X` let `η = 1` and the weight of the lowest `K`-type of `k` vanish; let this
weight be nonnegative, and at most `3 B` unless `U(η)` is compact.

Let `j : S →* U(ε) × U(η)` be a group homomorphism and write `j s = (g, g')`. Suppose that for
every `s`, `g - 1` lowers the flag of `v` with coefficient sum `σ s`, `g - 1` induces `g' - 1` on
the image of `i₀` modulo `v₁, …, v_d`, and the image of `j` contains `U(X)`, embedded diagonally.
Then `j` and `φ = σ - conj σ` satisfy the hypotheses `IsLaplaceDatum` of Laplace's method: `σ` is
automatically additive (by `LowersFlag.mul` and `IsPosition.lowersFlag_unique`), `φ` is additive
and imaginary and equals the difference of the phases at `(g - 1, g' - 1)`, and the traces of
`g - 1` and `g' - 1` agree. -/
theorem IsStationary.isLaplaceDatum [Fintype X] [DecidableEq X] {l : HCParam ε} {k : HCParam η}
    {M M' : ℕ} {e : X ⊕ Fin M ≃ n} {e' : X ⊕ Fin M' ≃ m} {B : ℝ}
    (hP : IsStationary l k e e' d v i₀) (h_steep : IsSteep l B e)
    (h_sign_inl : ∀ x : X, η (e' (Sum.inl x)) = 1)
    (h_weight_inl : ∀ x : X, k.lowestKType (e' (Sum.inl x)) = 0)
    (h_weight_nonneg : ∀ i : m, 0 ≤ k.lowestKType i)
    (h_weight_le : ∀ i i' : m, η i ≠ η i' → k.lowestKType i ≤ 3 * B)
    {S : Type} [Group S] {j : S →* USign ε × USign η} {σ : S → ℂ}
    (h_lowers : ∀ s : S, LowersFlag d v (subOnePair j s).1 (σ s))
    (h_induces : ∀ s : S, InducesOn d v i₀ (subOnePair j s).1 (subOnePair j s).2)
    (h_diag : ∀ u ∈ unitaryGroup X ℂ, ∃ s : S, subOnePair j s =
      (inclMatrix ℂ (e ∘ Sum.inl) * (u - 1) * (inclMatrix ℂ (e ∘ Sum.inl))ᴴ,
        inclMatrix ℂ (e' ∘ Sum.inl) * (u - 1) * (inclMatrix ℂ (e' ∘ Sum.inl))ᴴ)) :
    IsLaplaceDatum l k j (e' ∘ Sum.inl) B e (fun s : S ↦ σ s - conj (σ s)) := by
  -- Uniqueness of the flag-lowering sum makes `σ` additive on `S`.
  have h_mul (s₁ s₂ : S) : σ (s₁ * s₂) = σ s₁ + σ s₂ := by
    have h₁₂ : LowersFlag d v
        (((j s₁).1 : Matrix n n ℂ) * ((j s₂).1 : Matrix n n ℂ) - 1) (σ (s₁ * s₂)) := by
      simpa [map_mul] using h_lowers (s₁ * s₂)
    exact hP.lowersFlag_unique h₁₂ ((h_lowers s₁).mul (h_lowers s₂))
  -- Since `σ` is a homomorphism to the additive group of `ℂ`, it sends inverses to negatives.
  have h_inv (s : S) : σ s⁻¹ = -σ s :=
    (MonoidHom.mk' (Multiplicative.ofAdd ∘ σ) h_mul).map_inv s
  -- The adjoint of `(j s).1 - 1` is `(j s⁻¹).1 - 1`, which lowers the flag with the opposite sum.
  have h_adj (s : S) : LowersFlag d v (formAdjoint ε ε (subOnePair j s).1) (-σ s) := by
    simpa [formAdjoint_sub_one, map_inv, ← h_inv] using h_lowers s⁻¹
  exact
    { toIsSteep := h_steep
      phase_eq := fun s ↦ by
        rw [sub_eq_add_neg (σ s), ← map_neg]
        exact hP.phase_eq (h_lowers s) (h_induces s) (h_adj s)
      trace_eq := fun s ↦ hP.trace_eq (h_lowers s) (h_induces s) (h_adj s)
      phase_mul := fun s₁ s₂ ↦ by rw [h_mul, map_add, add_sub_add_comm]
      re_phase_eq_zero := fun s ↦ by simp
      sign_weight_right := fun x ↦ ⟨h_sign_inl x, h_weight_inl x⟩
      weight_nonneg_and_le := fun i i' ↦ ⟨h_weight_nonneg i, h_weight_le i i'⟩
      exists_diagonal := h_diag }

end New.DiscreteSeries

end

/-! ## Restriction to `U(ε)` -/

section RestrictionLemma

open Matrix Fintype MeasureTheory ComplexConjugate Norms.L2Operator

namespace New.DiscreteSeries

variable {n X : Type} [Fintype n] [DecidableEq n] [Fintype X] {ε : n → ℤˣ}

/-- Let `(v, i₀)` be a position of `U(ε)` in `U(ε ⊕ 1)` with one vector `v₁`, the only column of
`v`. If `v₁` has norm `1` for the form `ε ⊕ 1`, the matrix `(i₀, v₁)` preserves that form. -/
lemma IsPosition.gram_fromCols {v : Matrix (n ⊕ Unit) (Fin 1) ℂ} {i₀ : Matrix (n ⊕ Unit) n ℂ}
    (hP : IsPosition (Sum.elim ε 1) ε 0 v i₀)
    (h_norm : (vᴴ * signMatrix (Sum.elim ε (1 : Unit → ℤˣ)) * v) 0 0 = 1) :
    (fromCols i₀ (replicateCol Unit (v.col 0)))ᴴ * signMatrix (Sum.elim ε 1) *
      fromCols i₀ (replicateCol Unit (v.col 0)) = signMatrix (Sum.elim ε 1) := by
  have h_herm : ((fromCols i₀ (replicateCol Unit (v.col 0)))ᴴ * signMatrix (Sum.elim ε 1) *
      fromCols i₀ (replicateCol Unit (v.col 0))).IsHermitian :=
    isHermitian_conjTranspose_mul_mul _ (by simp [IsHermitian, signMatrix])
  refine Eq.trans ?_ (signMatrix_sum ε 1)
  -- The blocks: `i₀` is an isometry, `v₁` is orthogonal to its image (twice), `v₁` has norm `1`.
  ext (a | a) (b | b)
  · exact congrFun₂ hP.isometry a b
  · exact congrFun₂ hP.orthogonal a 0
  · rw [← h_herm.apply, fromBlocks_apply₂₁, Matrix.zero_apply, star_eq_zero]
    exact congrFun₂ hP.orthogonal b 0
  · exact h_norm.trans (by simp)

/-- For `w` in `U(ε ⊕ 1)` and `g` in `U(ε)`: `w (g ⊕ 1) w⁻¹ - 1 = w ((g - 1) ⊕ 0) w⁻¹`. -/
lemma conj_inl_sub_one (w : USign (Sum.elim ε (1 : Unit → ℤˣ))) (g : USign ε) :
    ((w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1 =
      (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) * fromBlocks ((g : Matrix n n ℂ) - 1) 0 0 0 *
        (↑(w⁻¹) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) := by
  have h_block : (U.inl ε (1 : Unit → ℤˣ) g : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1 =
      fromBlocks ((g : Matrix n n ℂ) - 1) 0 0 0 := by
    ext (a | a) (b | b) <;> simp [Matrix.one_apply]
  simp [← h_block, mul_sub_one, sub_mul]

/-- If `g` in `U(ε)` is within `1` of the identity, then `‖w (g ⊕ 1) w⁻¹‖ ≤ 1 + ‖w‖²` for `w` in
`U(ε ⊕ 1)`, in the `L²` operator norm. -/
lemma norm_conj_inl_le (w : USign (Sum.elim ε (1 : Unit → ℤˣ))) {g : USign ε}
    (hg : ‖(g : Matrix n n ℂ) - 1‖ ≤ 1) :
    ‖((w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ≤
      1 + ‖(w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 := by
  set W : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ := ↑w
  set Y : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ := fromBlocks ((g : Matrix n n ℂ) - 1) 0 0 0 with hY
  have hY_le : ‖Y‖ ≤ 1 := by rwa [hY, norm_fromBlocks_zero_zero, norm_zero,
    max_eq_left (norm_nonneg _)]
  calc ‖((w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖
      = ‖1 + W * Y * (↑(w⁻¹) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ := by
        rw [← conj_inl_sub_one w g, add_sub_cancel]
    _ ≤ 1 + ‖W‖ * ‖Y‖ * ‖W‖ := (norm_add_le _ _).trans
        (add_le_add norm_one.le (norm_mul₃_le.trans_eq (by rw [U.norm_inv w])))
    _ ≤ 1 + ‖W‖ * 1 * ‖W‖ := by gcongr
    _ = 1 + ‖W‖ ^ 2 := by ring

/-- For `w` in `U(ε ⊕ 1)` and `g` in `U(ε)`: `(w (g ⊕ 1) w⁻¹ - 1) w = w ((g - 1) ⊕ 0)`. -/
lemma conj_inl_sub_one_mul (w : USign (Sum.elim ε (1 : Unit → ℤˣ))) (g : USign ε) :
    (((w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1) *
        (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) =
      (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) * fromBlocks ((g : Matrix n n ℂ) - 1) 0 0 0 :=
  (Units.eq_mul_inv_iff_mul_eq _).1 (conj_inl_sub_one w g)

omit [DecidableEq n] in
private lemma mul_frame_blocks_iff
    {Y W : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ} {D : Matrix n n ℂ}
    {A : Matrix (n ⊕ Unit) n ℂ} {b : Matrix (n ⊕ Unit) Unit ℂ} (hw : W = fromCols A b) :
    Y * W = W * fromBlocks D 0 0 0 ↔ Y * A = A * D ∧ Y * b = 0 := by
  simp [hw, mul_fromCols, fromCols_mul_fromBlocks, fromCols_ext_iff]

/-- Let `w = (i₀, v₁)` lie in `U(ε ⊕ 1)`, where `v₁` is the only column of `v`. For `g` in `U(ε)`
the element `w (g ⊕ 1) w⁻¹` fixes `v₁`: its difference with `1` lowers the flag of `v`, with sum of
coefficients `0`. -/
lemma lowersFlag_conj_inl_sub_one {v : Matrix (n ⊕ Unit) (Fin 1) ℂ} {i₀ : Matrix (n ⊕ Unit) n ℂ}
    {w : USign (Sum.elim ε (1 : Unit → ℤˣ))}
    (hw : (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) = fromCols i₀ (replicateCol Unit (v.col 0)))
    (g : USign ε) :
    LowersFlag 0 v
      (((w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1)
      0 := by
  refine ⟨0, fun a ↦ a.elim0, ?_, Finset.sum_of_isEmpty _⟩
  rw [Matrix.mul_zero]
  ext i b
  obtain rfl : b = 0 := Fin.fin_one_eq_zero b
  exact congrFun₂ ((mul_frame_blocks_iff hw).mp (conj_inl_sub_one_mul w g)).2 i ()

/-- Let `w = (i₀, v₁)` lie in `U(ε ⊕ 1)`, where `v₁` is the only column of `v`. For `g` in `U(ε)`,
`InducesOn 0 v i₀` holds: `w (g ⊕ 1) w⁻¹ - 1` acts on the image of `i₀` as `g - 1`. So
`(w (g ⊕ 1) w⁻¹ - 1) i₀ = i₀ (g - 1)`. -/
lemma inducesOn_conj_inl_sub_one {v : Matrix (n ⊕ Unit) (Fin 1) ℂ} {i₀ : Matrix (n ⊕ Unit) n ℂ}
    {w : USign (Sum.elim ε (1 : Unit → ℤˣ))}
    (hw : (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) = fromCols i₀ (replicateCol Unit (v.col 0)))
    (g : USign ε) :
    InducesOn 0 v i₀
      (((w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1)
      ((g : Matrix n n ℂ) - 1) := by
  exact ⟨0, by simpa using ((mul_frame_blocks_iff hw).mp (conj_inl_sub_one_mul w g)).1⟩

/-- Let `w = (i₀, v₁)` lie in `U(ε ⊕ 1)`. Then `w (g ⊕ 1) w⁻¹ - 1 = i₀ (g - 1) i₀†`, where
`i₀† = formAdjoint (ε ⊕ 1) ε i₀`: conjugation by `w` acts as `g` on the image of `i₀` and fixes
its orthogonal complement. -/
lemma conj_inl_sub_one_eq_mul_formAdjoint {v : Matrix (n ⊕ Unit) (Fin 1) ℂ}
    {i₀ : Matrix (n ⊕ Unit) n ℂ} {w : USign (Sum.elim ε (1 : Unit → ℤˣ))}
    (hw : (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) = fromCols i₀ (replicateCol Unit (v.col 0)))
    (g : USign ε) :
    ((w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1 =
      i₀ * ((g : Matrix n n ℂ) - 1) * formAdjoint (Sum.elim ε (1 : Unit → ℤˣ)) ε i₀ := by
  -- The inverse `w⁻¹ = w†` has top block `i₀†`.
  have hw_inv : ((↑(w⁻¹) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)).toRows₁ =
      formAdjoint (Sum.elim ε (1 : Unit → ℤˣ)) ε i₀ := by
    rw [← formAdjoint_val]
    ext a b
    simp [formAdjoint, signMatrix, hw, diagonal_mul, mul_diagonal]
  rw [conj_inl_sub_one, hw, fromCols_mul_fromBlocks,
    ← fromRows_toRows (↑(w⁻¹) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ), fromCols_mul_fromRows, hw_inv]
  simp

omit [Fintype X] [DecidableEq n] in
/-- If `l` is steep (so its weight is `0` on `X` and in `[-3 B, -B]` elsewhere) and has a large gap,
the weight of the lowest `K`-type of `-l` lies in `[0, 3 B]`. -/
lemma IsSteep.lowestKType_neg_mem {B : ℝ} {l : HCParam ε} {M h : ℕ} {e : X ⊕ Fin M ≃ n}
    (h_steep : IsSteep l B e) (hl_gap : l.HasLargeGap h) (hB : 0 ≤ B) (i : n) :
    ((-l).lowestKType i : ℝ) ∈ Set.Icc 0 (3 * B) := by
  obtain ⟨x | a, rfl⟩ := e.surjective i
  · simpa [h_steep.weight_eq_zero] using hB
  · obtain ⟨h_lower, h_upper⟩ := h_steep.weight_mem a
    have h_neg : ((-l).lowestKType (e (Sum.inr a)) : ℝ) = -l.lowestKType (e (Sum.inr a)) := by simp
    exact ⟨by linarith, by linarith⟩

/-- If the entries of `i₀` and of the only column of `v` have norm at most `R`, then the square
matrix `(i₀, v)` of size `card n + 1` has squared operator norm at most `(card n + 1)⁴ R²`. -/
lemma sq_norm_fromCols_le {v : Matrix (n ⊕ Unit) (Fin 1) ℂ} {i₀ : Matrix (n ⊕ Unit) n ℂ} {R : ℝ}
    (hv : ∀ (i : n ⊕ Unit) (a : Fin 1), ‖v i a‖ ≤ R)
    (hi₀ : ∀ (i : n ⊕ Unit) (a : n), ‖i₀ i a‖ ≤ R) :
    ‖fromCols i₀ (replicateCol Unit (v.col 0))‖ ^ 2 ≤ card (n ⊕ Unit) ^ 4 * R ^ 2 := by
  calc _ ≤ (card (n ⊕ Unit) * card (n ⊕ Unit) * R) ^ 2 := by
        gcongr
        refine l2_opNorm_le_of_apply fun i a ↦ ?_
        rcases a with a | a
        exacts [hi₀ i a, hv i 0]
    _ = card (n ⊕ Unit) ^ 4 * R ^ 2 := by ring

/-- Let the integer vectors `l = 2 λ` for `U(ε)` and `-l'` for `U(ε ⊕ 1)` be steep with `B ≥ 1`: on
`X` the signs are `+1` and the weight of the lowest `K`-type is `0`; on the other `M`, resp.
`M + 1`, coordinates the signs are `+, -, +, …` and the weight decreases strictly in `[-3 B, -B]`.
Let `M` be even and let `λ` be a Harish-Chandra parameter with gap `500 (card n)³ + h` between
entries of opposite signs. Then `-l'`, `-l` have a stationary position with one vector `v`: an
isometry `i₀` of `(ℂ^n, ε)` into the orthogonal complement of `v`, the identity on `ℂ^X`, with
`i₀† μ' i₀ = μ` for the weights `μ'`, `μ` of `-l'`, `-l` as diagonal matrices. The form of signs
`ε ⊕ 1` has value `1` at `v`, and the entries of `v`, `i₀` have modulus at most `(6 B) ^ (M + 1)`.
-/
lemma IsSteep.exists_isStationary_conjTranspose_mul_mul_eq_one {B : ℝ} {l : HCParam ε}
    {l' : HCParam (Sum.elim ε (1 : Unit → ℤˣ))} {M h : ℕ} {e : X ⊕ Fin M ≃ n}
    {e' : X ⊕ Fin (M + 1) ≃ n ⊕ Unit} (hM : Even M) (h_steep : IsSteep l B e)
    (h_steep' : IsSteep (-l') B e') (hB : 1 ≤ B) (hl_gap : l.HasLargeGap h) :
    ∃ (v : Matrix (n ⊕ Unit) (Fin 1) ℂ) (i₀ : Matrix (n ⊕ Unit) n ℂ),
      IsStationary (-l') (-l) e' e 0 v i₀ ∧
      (vᴴ * signMatrix (Sum.elim ε (1 : Unit → ℤˣ)) * v) 0 0 = 1 ∧
      (∀ (i : n ⊕ Unit) (a : Fin 1), ‖v i a‖ ≤ (6 * B) ^ (M + 1)) ∧
      ∀ (i : n ⊕ Unit) (a : n), ‖i₀ i a‖ ≤ (6 * B) ^ (M + 1) := by
  classical
  have h_mono : StrictMono fun a : Fin M ↦ (-l).lowestKType (e (Sum.inr a)) := by
    simpa using h_steep.weight_strictAnti.neg
  obtain ⟨v, i₀, hP, h_norm, h_vec_le, h_isometry_le, -⟩ :=
    h_steep'.exists_isStationary (k := -l) (d := 0) hB rfl h_steep.sign_inl
      (by simp [h_steep.weight_eq_zero]) h_steep.sign_inr h_mono (by linarith) fun a ↦
        h_steep.lowestKType_neg_mem hl_gap (by linarith) (e (Sum.inr a))
  rw [show 6 * B = 3 * B + 3 * B by ring]
  -- The form takes the value `(-1) ^ M` at `v`, and `M` is even.
  exact ⟨v, i₀, hP, h_norm.trans hM.neg_one_pow, h_vec_le, h_isometry_le⟩

/-- **Restriction.** Let the parameter `l = 2 λ` of `U(ε)` be steep for `(X, M, B)` with `M` even
and `B ≥ 1`, and let `l' = 2 λ'` be a parameter of `U(ε ⊕ 1)` with `-l'` steep for `(X, M + 1, B)`.
With `n = card n`, let `HasLargeGap h` hold for both: the entries of `l` (resp. `l'`) are distinct
and of the parity of `n - 1` (resp. `n`), and two entries of `λ` (resp. `λ'`) at coordinates of
opposite sign differ by at least `500 n³ + h` (resp. `500 (n + 1)³ + h`). Let the entries of `l`,
`l'` be bounded by `L`, let `β ≥ 10¹²` bound `2 n + 1 + L` and `(n + 1)⁴ (6 B) ^ (2 M + 2)`, and let
`h ≥ 10³⁰ ((2 n + 1)² log β)³`.

Let `c_l`, `c_l'` be the discrete series coefficients `HCParam.dsCoeff`, given by Flensted-Jensen's
integral over the maximal compact subgroup, divided by the squared norm of the lowest `K`-type. The
measure `volume` on `U(ε)` is the Haar measure `haarU` made from Lebesgue measure by a Cayley chart,
with the compact dual normalisation. Then some `y` in `U(ε ⊕ 1)` with `‖y‖² ≤ β` has:
`β ^ (20 (2 n + 1)²)` times the modulus of the integral over `U(ε)` of
`c_l g * conj (c_l' (y⁻¹ (g ⊕ 1) y))` is at least the volume of `{g | ‖g - 1‖ ≤ 1}`. -/
theorem IsSteep.exists_volume_le_mul_norm_integral_dsCoeff [Nonempty n] {B β : ℝ} {l : HCParam ε}
    {l' : HCParam (Sum.elim ε (1 : Unit → ℤˣ))} {M L h : ℕ} {e : X ⊕ Fin M ≃ n}
    {e' : X ⊕ Fin (M + 1) ≃ n ⊕ Unit} (hM : Even M)
    (h_steep : IsSteep l B e) (h_steep' : IsSteep (-l') B e') (hB : 1 ≤ B)
    (hl : l.HasLargeGap h) (hl' : l'.HasLargeGap h)
    (hL : ∀ a : n, |l a| ≤ L) (hL' : ∀ a : n ⊕ Unit, |l' a| ≤ L) (hβ : 10 ^ 12 ≤ β)
    (hn : card (n ⊕ Unit) + card n + L ≤ β)
    (h_size : card (n ⊕ Unit) ^ 4 * (6 * B) ^ (2 * M + 2) ≤ β)
    (hh : 10 ^ 30 * ((card (n ⊕ Unit) + card n) ^ 2 * β.log) ^ 3 ≤ h) :
    ∃ y : USign (Sum.elim ε (1 : Unit → ℤˣ)),
      ‖(y : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 ≤ β ∧
      volume.real {g : USign ε | ‖(g : Matrix n n ℂ) - 1‖ ≤ 1} ≤
        β ^ (20 * (card (n ⊕ Unit) + card n) ^ 2) *
          ‖∫ g : USign ε, l.dsCoeff g *
            conj (l'.dsCoeff (y⁻¹ * U.inl ε 1 g * y : USign (Sum.elim ε 1)))‖ := by
  -- Take a stationary position `(v, i₀)` of `U(ε)` in `U(ε ⊕ 1)` for the parameters `-l'`, `-l`,
  -- put `w = (i₀, v)` and `y = w⁻¹`, and bound the period over its group `w U(ε) w⁻¹` from below.
  classical
  have h_mem (i : n) : ((-l).lowestKType i : ℝ) ∈ Set.Icc 0 (3 * B) :=
    h_steep.lowestKType_neg_mem hl (by linarith) i
  obtain ⟨v, i₀, hP, h_norm, h_vec_le, h_isometry_le⟩ :=
    h_steep.exists_isStationary_conjTranspose_mul_mul_eq_one hM h_steep' hB hl
  let w : USign (Sum.elim ε (1 : Unit → ℤˣ)) :=
    U.of IsHermitianInvolution.isUnit (fromCols i₀ (replicateCol Unit (v.col 0)))
      (hP.gram_fromCols h_norm)
  have hw : (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) = fromCols i₀ (replicateCol Unit (v.col 0)) :=
    rfl
  have hw_norm : ‖(w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 ≤ β :=
    calc _ ≤ card (n ⊕ Unit) ^ 4 * ((6 * B) ^ (M + 1)) ^ 2 :=
          sq_norm_fromCols_le h_vec_le h_isometry_le
      _ ≤ β := le_of_eq_of_le (by ring) h_size
  -- The homomorphism `j g = (w (g ⊕ 1) w⁻¹, g)` gives a Laplace datum for the stationary position.
  let j : USign ε →* USign (Sum.elim ε (1 : Unit → ℤˣ)) × USign ε :=
    ((MulAut.conj w).toMonoidHom.comp (U.inl ε 1)).prod (MonoidHom.id (USign ε))
  have h_proper : IsProperMap fun g : USign ε ↦ (j g).1 :=
    (Homeomorph.smul (ConjAct.toConjAct w)).isProperMap.comp isProperMap_inl
  have h_zero (x : X) : (-l).lowestKType (e (Sum.inl x)) = 0 := by simp [h_steep.weight_eq_zero]
  have h_lowers (g : USign ε) : LowersFlag 0 v (subOnePair j g).1 0 :=
    lowersFlag_conj_inl_sub_one hw g
  have h_induces (g : USign ε) : InducesOn 0 v i₀ (subOnePair j g).1 (subOnePair j g).2 :=
    inducesOn_conj_inl_sub_one hw g
  have h_datum : IsLaplaceDatum (-l') (-l) j (e ∘ Sum.inl) B e' (fun _ ↦ 0 - conj 0) :=
    hP.isLaplaceDatum h_steep' h_steep.sign_inl h_zero
      (fun i ↦ mod_cast (h_mem i).left) (fun i _ _ ↦ (h_mem i).right) h_lowers h_induces
      (hP.exists_diagonal_of_exists_ext h_steep'.sign_inl h_steep.sign_inl fun y ↦
        ⟨y, rfl, conj_inl_sub_one_eq_mul_formAdjoint hw y⟩)
  let Large : Set (USign ε) := {g : USign ε |
    ‖((j g).1 : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ≤ β + 1 ∧ ‖((j g).2 : Matrix n n ℂ)‖ ≤ β + 1}
  have h_period : volume Large ≤ ENNReal.ofReal (β ^ (20 * (card (n ⊕ Unit) + card n) ^ 2) *
      ‖∫ g : USign ε, (-l').laplaceIntegrand (-l) j (fun _ ↦ 0 - conj 0) g‖) :=
    (h_datum.laplace_method volume h_proper continuous_id hl'.neg hl.neg hB
      (by simpa using hL') (by simpa using hL) hβ hn hh).2
  -- The function `laplaceIntegrand` is the integrand of the pairing, and the ball `‖g - 1‖ ≤ 1`
  -- lies in the set whose volume `h_period` bounds.
  have h_integrand (g : USign ε) : (-l').laplaceIntegrand (-l) j (fun _ ↦ 0 - conj 0) g =
      l.dsCoeff g * conj (l'.dsCoeff (w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1))) := by
    rw [HCParam.laplaceIntegrand, dsCoeff_neg hl, dsCoeff_neg hl']
    simp [j, mul_comm]
  have h_ball : {g : USign ε | ‖(g : Matrix n n ℂ) - 1‖ ≤ 1} ⊆ Large := fun g hg ↦
    ⟨(norm_conj_inl_le w hg).trans (by linarith),
      by
        change ‖(g : Matrix n n ℂ)‖ ≤ β + 1
        refine (norm_le_norm_add_norm_sub' _ 1).trans ?_
        rw [norm_one]
        exact add_le_add (by linarith) hg⟩
  refine ⟨w⁻¹, by rwa [U.norm_inv], ENNReal.toReal_le_of_le_ofReal (by positivity) ?_⟩
  simpa only [h_integrand, inv_inv] using (measure_mono h_ball).trans h_period

end New.DiscreteSeries

end RestrictionLemma
