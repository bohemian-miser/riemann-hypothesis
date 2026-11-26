module

import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Group.Matrix
public import New.Appendix.DiscreteSeries.Localization
public import Lib.Adelic.Unitary.ComponentsAndBlockSums
import Lib.DiscreteSeries.FlenstedJensen.PsiKTypes
import Lib.DiscreteSeries.FlenstedJensen.SquareIntegrability
import Lib.DiscreteSeries.Haar.TotalMass
public import Lib.General.LinearAlgebra.BlockEmbeddings
import New.Appendix.DiscreteSeries.GaussianShape

/-!
# Lower bounds for periods by Laplace's method

This file proves lower bounds for periods of discrete series coefficients. Let
`j : S →* U(ε) × U(η)` be a homomorphism and write `θ` for the function `laplaceIntegrand` on `S`.
Laplace's method bounds the volume of a large ball by a power of `β` times `‖∫ θ‖`, where `β` bounds
the dimensions and the entries of the parameters.

## Main definitions and results

* The values of `θ` lie in a cone about the positive real axis, up to an exponentially small error
  (`IsLaplaceDatum.norm_laplaceIntegrand_le_mul_re_add`). With the decay of the coefficients, `θ` is
  integrable and the volume of a large ball is at most a power of `β` times `‖∫ θ‖`
  (`IsLaplaceDatum.laplace_method`).
* `exists_lagrange_weights`: Lagrange interpolation weights `c k ≥ 1` for strictly decreasing
  integer nodes, used both here for codimension-1 restriction and in
  `New.Spanning.Bessel.LargeFunction` for the Bessel period.
* `IsSteep.exists_isLaplaceDatum_restriction` and
  `IsSteep.exists_volume_le_mul_norm_integral_dsCoeff`:
  for steep parameters `l` on `U(ε)` and `-l'` on `U(ε ⊕ 1)` (with `M` even), an explicit signed
  Cauchy matrix `ω ∈ U(ε ⊕ 1)` built from Lagrange weights makes `j g = (g, ω⁻¹ (g ⊕ 1) ω)` satisfy
  `IsLaplaceDatum` directly with zero phase, bounding the restriction pairing from below via
  `IsLaplaceDatum.laplace_method`.

Notions from other files:
* `USign ε` is the unitary group `U(ε)` of the diagonal form with signs `ε`, and
  `U.sum (signMatrix_sum ε η)` is the block embedding `(g, g') ↦ g ⊕ g'` of `U(ε) × U(η)`.
* `l.dsCoeff g` is the discrete series coefficient with doubled Harish-Chandra parameter
  `l = 2λ : HCParam ε`, given by Flensted-Jensen's integral and normalised to take the value `1`
  at the identity; `l.lowestKType` is the highest weight of its lowest `K`-type. On the maximal
  compact subgroup it is the coefficient at the highest weight vector of this `K`-type
  (`New.dsCoeff_of_mem_maxCompactU`).
* A parameter `l = 2λ` indexed by `n` has gap `A` if its entries are distinct and congruent to
  `card n - 1` mod 2, and `|λ a - λ b| ≥ A` whenever `ε a ≠ ε b`; `l.HasLargeGap h` says that `l`
  has gap `500 (card n)³ + h`.
* `l.laplaceIntegrand k j φ s` is the coefficient of `l` at the first component of `j s`, times the
  conjugate of the coefficient of `k` at the second, times `exp (-φ s)`.
* `IsLaplaceDatum l k j τ B e φ` collects the hypotheses of Laplace's method. Let `μ`, `μ'` be the
  weights `l.lowestKType`, `k.lowestKType` and let `j s = (g, g')`.
  - The parameter `l` is steep (`IsSteep`) for the splitting `e : X ⊕ Fin M ≃ n`: on `X` the sign is
    `+1` and `μ` is `0`; on the other `M` indices the signs are `+, -, +, …` and `μ` decreases
    strictly in `[-3 B, -B]`.
  - The weight `μ'` is nonnegative, at most `3 B` if `η` takes both signs, and `0` on the image of
    `τ : X → m`, where the sign is `+1`.
  - The phase `φ s = tr (μ (g - 1)) - tr (μ' (g' - 1))` is additive and imaginary, and
    `tr (g - 1) = tr (g' - 1)`.
  - For each unitary `u` indexed by `X` there is an `s` such that `g - 1` and `g' - 1` are `u - 1`
    extended by zero along `e` and along `τ`.

## Relation to the literature

This file is the step of Laplace's method that makes restriction periods explicitly large. Near 1 a
discrete series coefficient of U(p,q) is an explicit phase times a number close to the interval
[0,1], up to a tenth of its size and an exponentially small error, so that the losses at the
archimedean places are at most powers of the weights. The integral formula for coefficients,
non-vanishing of periods and fixed-rank asymptotics for coherent states are known in the literature.
Related work: Nelson–Venkatesh, The orbit method and analysis of automorphic forms, 2021; H. He, On
the Gan–Gross–Prasad conjecture for U(p,q), 2017; B. Sun, Matrix coefficients of cohomologically
induced representations, 2007.
-/

@[expose] public section

section LaplaceMethod

open Matrix Fintype Complex Real MeasureTheory ComplexConjugate New.HCParam

namespace New.DiscreteSeries

/-- Let `a, c, t ∈ [0, 1]`. If `u` is within `a / 10 + t` of `a` and `v` within `c / 10 + t` of `c`,
then `u v` is within `0.21 a c + 4 t` of `a c`. -/
lemma norm_mul_sub_mul_le {a c t : ℝ} {u v : ℂ} (ha : a ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1)
    (ht : t ∈ Set.Icc 0 1) (hu : ‖u - a‖ ≤ a / 10 + t) (hv : ‖v - c‖ ≤ c / 10 + t) :
    ‖u * v - ↑(a * c)‖ ≤ 0.21 * (a * c) + 4 * t := by
  calc ‖u * v - ↑(a * c)‖
      = ‖a * (v - c) + (u - a) * c + (u - a) * (v - c)‖ := by rw [ofReal_mul]; ring_nf
    _ ≤ ‖a * (v - c)‖ + ‖(u - a) * c‖ + ‖(u - a) * (v - c)‖ := norm_add₃_le
    _ ≤ a * (c / 10 + t) + (a / 10 + t) * c + (a / 10 + t) * (c / 10 + t) := by
        simp only [norm_mul, Complex.norm_of_nonneg ha.1, Complex.norm_of_nonneg hc.1]
        gcongr <;> linarith [ha.1, hc.1, ht.1]
    _ ≤ 0.21 * (a * c) + 4 * t := by nlinarith [ha.1, hc.1, ht.1, ha.2, hc.2, ht.2]

/-- A complex number `z` within `0.21 p + 4 t` of a real number `p ≥ 0` lies in the cone
`‖z‖ ≤ 2 re z + 12 t`. -/
lemma norm_le_two_mul_re_add {p t : ℝ} {z : ℂ} (hp : 0 ≤ p) (hz : ‖z - p‖ ≤ 0.21 * p + 4 * t) :
    ‖z‖ ≤ 2 * z.re + 12 * t := by
  have h_norm : ‖z‖ ≤ p + ‖z - p‖ := by
    simpa [abs_of_nonneg hp] using norm_le_insert' z p
  have h_re : -‖z - p‖ ≤ z.re - p := by simpa using neg_le_of_abs_le (abs_re_le_norm (z - p))
  linarith

/-- If `T ≥ 1`, `T ρ = 10⁻¹³` and `h ≥ 10³⁰ T³`, then `(1 + ρ²) ^ (-h) ≤ exp (-100 T) ^ 4`. -/
lemma inv_one_add_sq_pow_le_exp_pow_four {T ρ : ℝ} {h : ℕ} (hT : 1 ≤ T) (hρ : T * ρ = 1e-13)
    (hh : 10 ^ 30 * T ^ 3 ≤ h) : (1 + ρ ^ 2)⁻¹ ^ h ≤ rexp (-100 * T) ^ 4 := by
  -- Take logarithms: `log (1 + ρ²) ≥ 2 ρ² / (ρ² + 2)`, `h ≥ 10³⁰ T³` and `ρ² T² = 10⁻²⁶`.
  have hρ_pos : 0 < ρ := by nlinarith
  have hρ_le : ρ ≤ 100⁻¹ := by nlinarith
  have h_gap : 400 * T ≤ 10 ^ 30 * T ^ 3 * (2 * ρ ^ 2 / (ρ ^ 2 + 2)) := by
    have h_sq : T ^ 2 * ρ ^ 2 = 1e-13 ^ 2 := by rw [← mul_pow, hρ]
    field_simp
    nlinarith
  have h_logs : 400 * T ≤ h * (1 + ρ ^ 2).log :=
    h_gap.trans (mul_le_mul hh (le_log_one_add_of_nonneg (sq_nonneg ρ)) (by positivity)
      (Nat.cast_nonneg h))
  rw [← log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_inv,
    Real.log_exp, Nat.cast_ofNat]
  linarith

/-- Let `β ≥ 16`, `N ≥ 1` and `V, I ≥ 0`; in the application `V` and `W` are the volumes of a large
and a small ball and `I` is the norm of an integral. If `V ≤ β ^ (16 N) W` and
`W / 4 ≤ 2 I + 6 β ^ (-50 N) 16 ^ (9 N) V`, then `V ≤ β ^ (20 N) I`, as the error term contributes
at most `V / 2`. -/
lemma le_pow_mul_of_le {β : ℝ} {N : ℕ} {V W I : ℝ} (hβ : 16 ≤ β) (hN : 1 ≤ N) (hV : 0 ≤ V)
    (hI : 0 ≤ I) (h_cover : V ≤ β ^ (16 * N) * W)
    (h_int : W / 4 ≤ 2 * I + 6 * β⁻¹ ^ (50 * N) * (16 ^ (9 * N) * V)) :
    V ≤ β ^ (20 * N) * I := by
  have hβ_one : 1 ≤ β := by linarith
  have h_main : 16 * β ^ (16 * N) ≤ β ^ (20 * N) :=
    calc 16 * β ^ (16 * N) ≤ β * β ^ (16 * N) := by gcongr
      _ ≤ β ^ (20 * N) := by
          rw [← pow_succ']
          exact pow_le_pow_right₀ hβ_one (by omega)
  have h_error : 48 * β ^ (16 * N) * 16 ^ (9 * N) ≤ β ^ (50 * N) :=
    calc 48 * β ^ (16 * N) * 16 ^ (9 * N) ≤ β ^ 2 * β ^ (16 * N) * β ^ (9 * N) := by
          gcongr
          nlinarith
      _ ≤ β ^ (50 * N) := by
          rw [← pow_add, ← pow_add]
          exact pow_le_pow_right₀ hβ_one (by omega)
  have h_half : β ^ (16 * N) * (24 * β⁻¹ ^ (50 * N) * 16 ^ (9 * N)) ≤ 1 / 2 := by
    rw [inv_pow]
    field_simp
    linarith
  have h_combined : V ≤ 8 * β ^ (16 * N) * I + 1 / 2 * V :=
    calc V ≤ β ^ (16 * N) * (8 * I + 24 * β⁻¹ ^ (50 * N) * 16 ^ (9 * N) * V) := by
          refine h_cover.trans ?_
          gcongr
          linarith
      _ = 8 * β ^ (16 * N) * I + β ^ (16 * N) * (24 * β⁻¹ ^ (50 * N) * 16 ^ (9 * N)) * V := by ring
      _ ≤ 8 * β ^ (16 * N) * I + 1 / 2 * V := by gcongr
  linarith [mul_le_mul_of_nonneg_right h_main hI]

/-- If `N ≥ 1`, `t ≥ 1` and `h ≥ 10³⁰ (N t)³`, then `h ≥ 18 N`. -/
lemma eighteen_mul_le_of_mul_pow_three_le {N h : ℕ} {t : ℝ} (hN : 1 ≤ N) (ht : 1 ≤ t)
    (hh : 10 ^ 30 * (N * t) ^ 3 ≤ h) : 18 * N ≤ h := by
  have h_cube : N * t ≤ (N * t) ^ 3 :=
    le_self_pow₀ (one_le_mul_of_one_le_of_one_le (mod_cast hN) ht) three_ne_zero
  exact_mod_cast (by nlinarith : (18 * N : ℝ) ≤ h)

section Modulus

variable {n m X S : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype X]
  [DecidableEq X] [Group S] {ε : n → ℤˣ} {η : m → ℤˣ} {l : HCParam ε} {k : HCParam η} {τ : X → m}
  {B T ρ : ℝ} {M h : ℕ} {e : X ⊕ Fin M ≃ n} {j : S →* USign ε × USign η} {φ : S → ℂ}

/-- Under `IsLaplaceDatum` the phase `φ` is imaginary, so the factor `exp (-φ s)` of
`laplaceIntegrand` has modulus one, and the modulus at `s` is the product of the moduli of the
discrete series coefficients at the two components of `j s`. -/
lemma IsLaplaceDatum.norm_laplaceIntegrand (h_datum : IsLaplaceDatum l k j τ B e φ) (s : S) :
    ‖l.laplaceIntegrand k j φ s‖ = ‖l.dsCoeff (j s).1‖ * ‖k.dsCoeff (j s).2‖ := by
  simp [laplaceIntegrand, Complex.norm_exp, h_datum.re_phase_eq_zero]

open Norms.Frobenius in
/-- **Away from the maximal compact subgroup.** Let `j` and `φ` satisfy `IsLaplaceDatum` (so `φ` is
imaginary), let `T ≥ 1` and `T ρ = 10⁻¹³`, and let both doubled parameters `l`, `k` have gap
`500 · (dimension)³ + h` with `h ≥ 10³⁰ T³`. If the noncompact parts `y`, `y'` of the components of
`j s` (the entries that join indices of opposite signs) have `‖y‖² + ‖y'‖² ≥ ρ²` in the Frobenius
norm, then `laplaceIntegrand` has modulus at most `exp (-100 T)` at `s`. -/
lemma IsLaplaceDatum.norm_laplaceIntegrand_le_of_far (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hl : l.HasLargeGap h) (hk : k.HasLargeGap h) (hT : 1 ≤ T) (hρ : T * ρ = 1e-13)
    (hh : 10 ^ 30 * T ^ 3 ≤ h) {s : S}
    (h_far : ρ ^ 2 ≤ ‖noncompactPart ε (j s).1‖ ^ 2 + ‖noncompactPart η (j s).2‖ ^ 2) :
    ‖l.laplaceIntegrand k j φ s‖ ≤ rexp (-100 * T) := by
  set y : ℝ := ‖noncompactPart ε (j s).1‖
  set y' : ℝ := ‖noncompactPart η (j s).2‖
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (exp_nonneg _) four_ne_zero).1 ?_
  calc ‖l.laplaceIntegrand k j φ s‖ ^ 4 = ‖l.dsCoeff (j s).1‖ ^ 4 * ‖k.dsCoeff (j s).2‖ ^ 4 := by
        rw [h_datum.norm_laplaceIntegrand, mul_pow]
    _ ≤ (1 + y ^ 2)⁻¹ ^ h * (1 + y' ^ 2)⁻¹ ^ h := by
        gcongr
        exacts [norm_dsCoeff_pow_four_le (hg := hl) _, norm_dsCoeff_pow_four_le (hg := hk) _]
    _ ≤ (1 + ρ ^ 2)⁻¹ ^ h := by
        rw [← mul_pow, ← mul_inv]
        gcongr
        linarith [mul_nonneg (sq_nonneg y) (sq_nonneg y')]
    _ ≤ rexp (-100 * T) ^ 4 := inv_one_add_sq_pow_le_exp_pow_four hT hρ hh

/-- The matrix of the block sum `U.sum (signMatrix_sum ε η) g` of `g.1` in `U(ε)` and `g.2` in
`U(η)` is the block diagonal matrix `fromBlocks g.1 0 0 g.2`. -/
lemma coe_sum_eq_fromBlocks (g : USign ε × USign η) :
    (U.sum (signMatrix_sum ε η) g : Matrix (n ⊕ m) (n ⊕ m) ℂ) =
      fromBlocks (g.1 : Matrix n n ℂ) 0 0 (g.2 : Matrix m m ℂ) :=
  rfl

open Norms.L2Operator in
/-- The operator norm of the block sum `g.1 ⊕ g.2` of elements of the unitary groups `U(ε)` and
`U(η)` is the larger of the two norms. -/
lemma norm_coe_sum_eq_max (g : USign ε × USign η) :
    ‖(U.sum (signMatrix_sum ε η) g : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖ =
      max ‖(g.1 : Matrix n n ℂ)‖ ‖(g.2 : Matrix m m ℂ)‖ := by
  rw [coe_sum_eq_fromBlocks, norm_fromBlocks_zero_zero]

open Norms.L2Operator in
/-- The distance to `1`, in the operator norm, of the block sum `g.1 ⊕ g.2` of elements of the
unitary groups `U(ε)` and `U(η)` is the larger of the two distances to `1`. -/
lemma norm_sum_sub_one (g : USign ε × USign η) :
    ‖(U.sum (signMatrix_sum ε η) g : Matrix (n ⊕ m) (n ⊕ m) ℂ) - 1‖ =
      max ‖(g.1 : Matrix n n ℂ) - 1‖ ‖(g.2 : Matrix m m ℂ) - 1‖ := by
  rw [← norm_fromBlocks_zero_zero, coe_sum_eq_fromBlocks]
  congr 1
  ext (a | a) (b | b) <;> simp [Matrix.one_apply]

end Modulus

/-- Let `j s = (g, g')` in `U(ε) × U(η)`. If `s ↦ g` is proper and `s ↦ g'` is continuous, then the
block diagonal sum `s ↦ g ⊕ g'` is a proper map to `U(ε ⊕ η)`. -/
lemma isProperMap_sum {n m S : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [Group S] {ε : n → ℤˣ} {η : m → ℤˣ} {j : S →* USign ε × USign η} [TopologicalSpace S]
    (hj : IsProperMap fun s : S ↦ (j s).1) (hj' : Continuous fun s : S ↦ (j s).2) :
    IsProperMap ((U.sum (signMatrix_sum ε η)).comp j) := by
  have hj_cont : Continuous fun s : S ↦ (j s).1 := hj.continuous
  have h_cont : Continuous ((U.sum (signMatrix_sum ε η)).comp j) := by
    simp only [U.sum, MonoidHom.coe_comp, continuous_U_iff_matrix, Function.comp_apply,
      MonoidHom.codRestrict_apply, MonoidHom.coe_prodMap, Subgroup.coe_subtype, val_blockGL_apply,
      Prod.map_fst, Prod.map_snd]
    fun_prop
  -- Composing with the upper left block gives back the proper map `s ↦ g`.
  let block (x : USign (Sum.elim ε η)) : Matrix n n ℂ :=
    (x : Matrix (n ⊕ m) (n ⊕ m) ℂ).toBlocks₁₁
  have h_comp : IsProperMap (block ∘ (U.sum (signMatrix_sum ε η)).comp j) := by
    change IsProperMap ((fun g : USign ε ↦ (g : Matrix n n ℂ)) ∘ fun s : S ↦ (j s).1)
    exact isClosedEmbedding_U.isProperMap.comp hj
  exact isProperMap_of_comp_of_t2 h_cont (by fun_prop [toBlocks₁₁]) h_comp

open Norms.L2Operator in
/-- Let `j` and `φ`, defined on a group `S`, satisfy `IsLaplaceDatum` (so `φ` is imaginary). Let the
doubled parameters `l`, `k` have gap `500 · (dimension)³ + h` and entries bounded by `L`, with
`card n + card m + L ≤ β`. Suppose `j s = (g, g')` and the block diagonal sum `g ⊕ g'` is within
`(200 β⁵)⁻¹` of `1` in the operator norm. Then `laplaceIntegrand` at `s` has norm at least `1 / 4`,
as each coefficient has norm at least `1 / 2`. -/
lemma IsLaplaceDatum.one_div_four_le_norm_laplaceIntegrand {n m X S : Type} [Fintype n]
    [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype X] [DecidableEq X] [Group S] [Nonempty n]
    [Nonempty m] {ε : n → ℤˣ} {η : m → ℤˣ} {l : HCParam ε} {k : HCParam η} {τ : X → m} {B β : ℝ}
    {L M h : ℕ} {e : X ⊕ Fin M ≃ n} {j : S →* USign ε × USign η} {φ : S → ℂ}
    (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hl : l.HasLargeGap h) (hk : k.HasLargeGap h) (hl_le : ∀ a : n, |l a| ≤ L)
    (hk_le : ∀ a : m, |k a| ≤ L) (hβ_le : card n + card m + L ≤ β) {s : S}
    (hs : ‖(U.sum (signMatrix_sum ε η) (j s) : Matrix (n ⊕ m) (n ⊕ m) ℂ) - 1‖ ≤ (200 * β ^ 5)⁻¹) :
    1 / 4 ≤ ‖l.laplaceIntegrand k j φ s‖ := by
  have hn_pos : (1 : ℝ) ≤ card n := Nat.one_le_cast.2 Fintype.card_pos
  have hm_pos : (1 : ℝ) ≤ card m := Nat.one_le_cast.2 Fintype.card_pos
  obtain ⟨h_fst, h_snd⟩ : ‖((j s).1 : Matrix n n ℂ) - 1‖ ≤ (200 * β ^ 5)⁻¹ ∧
      ‖((j s).2 : Matrix m m ℂ) - 1‖ ≤ (200 * β ^ 5)⁻¹ := by
    rwa [norm_sum_sub_one, max_le_iff] at hs
  have hl_half : 2⁻¹ ≤ ‖l.dsCoeff (j s).1‖ := half_le_norm_dsCoeff hl_le (by linarith) h_fst
  have hk_half : 2⁻¹ ≤ ‖k.dsCoeff (j s).2‖ := half_le_norm_dsCoeff hk_le (by linarith) h_snd
  calc (1 / 4 : ℝ) = 2⁻¹ * 2⁻¹ := by norm_num
    _ ≤ ‖l.dsCoeff (j s).1‖ * ‖k.dsCoeff (j s).2‖ := by gcongr
    _ = ‖l.laplaceIntegrand k j φ s‖ := (h_datum.norm_laplaceIntegrand s).symm

variable {n m X S : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype X]
  [DecidableEq X] [Group S] [Nonempty n] [Nonempty m] {ε : n → ℤˣ} {η : m → ℤˣ} {l : HCParam ε}
  {k : HCParam η} {τ : X → m} {B β T : ℝ} {L M h : ℕ} {e : X ⊕ Fin M ≃ n}
  {j : S →* USign ε × USign η} {φ : S → ℂ}

section Cone

open Norms.Frobenius

/-- **The cone near the identity.** Let `j` and `φ` satisfy `IsLaplaceDatum`: in particular `φ` is
additive, and for `(g, g') = j s` it is `φ s = tr (μ (g - 1)) - tr (μ' (g' - 1))`. Let both
parameters have gap `500 · (dimension)³ + h` and entries bounded by `L`, let
`card n + card m + L ≤ β` and `log β ≥ 1`, put `T = (card n + card m)² log β` and let `δ T ≤ 10⁻¹²`.
If `g - 1` and `g' - 1` have Frobenius norm at most `δ`, then `z = laplaceIntegrand s` lies in the
cone `‖z‖ ≤ 2 re z + 12 exp (-100 T)`. -/
lemma IsLaplaceDatum.norm_laplaceIntegrand_le_mul_re_add_of_near
    (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hl : l.HasLargeGap h) (hk : k.HasLargeGap h) (hl_le : ∀ a : n, |l a| ≤ L)
    (hk_le : ∀ a : m, |k a| ≤ L) (hβ_le : card n + card m + L ≤ β) (h_log_β : 1 ≤ β.log)
    (hT : T = (card n + card m : ℝ) ^ 2 * β.log) {δ : ℝ} (hδ : δ * T ≤ 1e-12)
    {s : S} (h_fst : ‖((j s).1 : Matrix n n ℂ) - 1‖ ≤ δ)
    (h_snd : ‖((j s).2 : Matrix m m ℂ) - 1‖ ≤ δ) :
    ‖l.laplaceIntegrand k j φ s‖ ≤ 2 * (l.laplaceIntegrand k j φ s).re + 12 * rexp (-100 * T) := by
  -- The phases cancel, so the value is close to a product of two numbers in `[0, 1]`.
  have hn_pos : (1 : ℝ) ≤ card n := Nat.one_le_cast.2 Fintype.card_pos
  have hm_pos : (1 : ℝ) ≤ card m := Nat.one_le_cast.2 Fintype.card_pos
  have hT_one : 1 ≤ T := by nlinarith
  have hδ_half : δ ≤ 2⁻¹ := by nlinarith [(norm_nonneg _).trans h_fst]
  have h_dim (d : ℝ) (hd : 1 ≤ d) (hd' : d + 1 ≤ card n + card m) :
      d ^ 2 ≤ T ∧ d ^ 2 * (d + L + 1).log ≤ T := by
    have h_sq : d ^ 2 ≤ (card n + card m : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h_log : (d + L + 1).log ≤ β.log := log_le_log (by positivity) (by linarith)
    refine ⟨by nlinarith, ?_⟩
    rw [hT]
    exact mul_le_mul h_sq h_log (log_nonneg (by linarith)) (sq_nonneg _)
  obtain ⟨hn_sq, hn_log⟩ := h_dim (card n) hn_pos (by linarith)
  obtain ⟨hm_sq, hm_log⟩ := h_dim (card m) hm_pos (by linarith)
  set ratio_l : ℂ := l.dsCoeff (j s).1 /
    cexp (intDiagonal l.lowestKType * logOneAdd (subOnePair j s).1).trace with h_ratio_l
  set ratio_k : ℂ := (-k).dsCoeff (j s).2 /
    cexp (intDiagonal (-k).lowestKType * logOneAdd (subOnePair j s).2).trace with h_ratio_k
  -- The phase at the matrix logarithms `logOneAdd` of the two components of `j s` is still `φ s`.
  have h_prod : l.laplaceIntegrand k j φ s = ratio_l * ratio_k := by
    have h_phase : l.phase k ((subOnePair j s).map logOneAdd logOneAdd) = φ s :=
      h_datum.phase_logOneAdd s (h_fst.trans hδ_half) (h_snd.trans hδ_half)
    rw [h_ratio_l, h_ratio_k, laplaceIntegrand, ← h_phase, dsCoeff_neg hk]
    -- Unfold the phase as a difference of traces and use `exp (x - y) = exp x / exp y`.
    simp [phase, intDiagonal, field, ← diagonal_neg, Complex.exp_sub, Complex.exp_neg]
  obtain ⟨a, ha, ha_near⟩ : ∃ a ∈ Set.Icc (0 : ℝ) 1, ‖ratio_l - a‖ ≤ a / 10 + rexp (-100 * T) :=
    exists_norm_dsCoeff_div_cexp_sub_le hl hl_le h_fst hT_one hn_sq hn_log hδ
  obtain ⟨c, hc, hc_near⟩ : ∃ c ∈ Set.Icc (0 : ℝ) 1, ‖ratio_k - c‖ ≤ c / 10 + rexp (-100 * T) :=
    exists_norm_dsCoeff_div_cexp_sub_le hk.neg (by simpa using hk_le) h_snd hT_one hm_sq hm_log hδ
  have h_exp : rexp (-100 * T) ∈ Set.Icc 0 1 := ⟨exp_nonneg _, exp_le_one_iff.2 (by linarith)⟩
  rw [h_prod]
  exact norm_le_two_mul_re_add (mul_nonneg ha.1 hc.1)
    (norm_mul_sub_mul_le ha hc h_exp ha_near hc_near)

/-- **The cone.** Let `j` and `φ` satisfy `IsLaplaceDatum` with `B ≥ 1`: the weight of the lowest
`K`-type of `l` is `0` on `X` and decreases in `[-3 B, -B]` elsewhere, that of `k` is nonnegative
and `0` on `X`, the difference `φ` of the two phases is additive and imaginary, and the image of `j`
contains `U(X)`, placed in the two factors by `e` and `τ`. Let the entries of `l` and `k` be bounded
by `L`, let `card n + card m + L ≤ β` and `log β ≥ 1`, and put `T = (card n + card m)² log β`. Let
both doubled parameters have gap `500 · (dimension)³ + h` with `h ≥ 10³⁰ T³`. Then every value `z`
of `laplaceIntegrand` at an `s`, with `j s = (g, g')`, satisfies
`‖z‖ ≤ 2 re z + 12 exp (-100 T)`. -/
lemma IsLaplaceDatum.norm_laplaceIntegrand_le_mul_re_add (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hl : l.HasLargeGap h)
    (hk : k.HasLargeGap h) (hB : 1 ≤ B) (hl_le : ∀ a : n, |l a| ≤ L) (hk_le : ∀ a : m, |k a| ≤ L)
    (hβ_le : card n + card m + L ≤ β) (h_log_β : 1 ≤ β.log)
    (hT : T = (card n + card m : ℝ) ^ 2 * β.log) (hh : 10 ^ 30 * T ^ 3 ≤ h) (s : S) :
    ‖l.laplaceIntegrand k j φ s‖ ≤ 2 * (l.laplaceIntegrand k j φ s).re + 12 * rexp (-100 * T) := by
  have hT_one : 1 ≤ T := by
    have h_card : (1 : ℝ) ≤ card n + card m := mod_cast Nat.add_pos_left Fintype.card_pos _
    nlinarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, T * ρ = 1e-13 := ⟨1e-13 / T, by field_simp⟩
  rcases le_total (‖noncompactPart ε (j s).1‖ ^ 2 + ‖noncompactPart η (j s).2‖ ^ 2) (ρ ^ 2) with
    h_near | h_far
  · -- By localization the value at `s` is also taken at a `t` with `j t` within `4 ρ` of `1`.
    have hρ_pos : 0 < ρ := by nlinarith
    have hρ_le : ρ ≤ 6⁻¹ := by nlinarith
    obtain ⟨t, hθ, h_fst, h_snd⟩ : ∃ t : S,
        l.laplaceIntegrand k j φ s = l.laplaceIntegrand k j φ t ∧
        ‖(subOnePair j t).1‖ ≤ 4 * ρ ∧ ‖(subOnePair j t).2‖ ≤ 4 * ρ :=
      h_datum.exists_laplaceIntegrand_eq_and_norm_subOnePair_le ρ hB hρ_pos hρ_le s h_near
    rw [hθ]
    exact h_datum.norm_laplaceIntegrand_le_mul_re_add_of_near hl hk hl_le hk_le hβ_le h_log_β hT
      (by linarith : 4 * ρ * T ≤ 1e-12) h_fst h_snd
  · -- Away from the maximal compact subgroups the gap makes the value itself small.
    have h_small : ‖l.laplaceIntegrand k j φ s‖ ≤ rexp (-100 * T) :=
      h_datum.norm_laplaceIntegrand_le_of_far hl hk hT_one hρ hh h_far
    linarith [exp_nonneg (-100 * T),
      neg_le_of_abs_le (abs_re_le_norm (l.laplaceIntegrand k j φ s))]

end Cone

open Norms.L2Operator

/-- **Decay.** Let `j` and `φ` satisfy `IsLaplaceDatum` (so `φ` is imaginary). Let `l` and `k`
satisfy `HasLargeGap h`, i.e. have gap `500 · (dimension)³ + h`. Let `c ≤ h` and `j s = (g, g')`,
and write `g ⊕ g'` for the block diagonal sum `U.sum (signMatrix_sum ε η) (j s)` in `U(ε ⊕ η)`. Then
the norm of `laplaceIntegrand` at `s` is at most `(2 / ‖g ⊕ g'‖) ^ c`, where `‖g ⊕ g'‖` is the
operator norm. -/
lemma IsLaplaceDatum.norm_laplaceIntegrand_le_pow (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hl : l.HasLargeGap h) (hk : k.HasLargeGap h) {c : ℕ} (hc : c ≤ h) (s : S) :
    ‖l.laplaceIntegrand k j φ s‖ ≤
      (2 / ‖(U.sum (signMatrix_sum ε η) (j s) : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖) ^ c := by
  -- Use the decay of the coefficient at the larger component; the other one is at most `1`.
  rw [h_datum.norm_laplaceIntegrand, norm_coe_sum_eq_max]
  rcases max_choice ‖((j s).1 : Matrix n n ℂ)‖ ‖((j s).2 : Matrix m m ℂ)‖ with h_max | h_max
  · rw [h_max]
    exact (mul_le_of_le_one_right (norm_nonneg _) (norm_dsCoeff_le_one hk _)).trans
      (norm_dsCoeff_le_pow hl (hc.trans le_add_self) _)
  · rw [h_max]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_dsCoeff_le_one hl _)).trans
      (norm_dsCoeff_le_pow hk (hc.trans le_add_self) _)

/-- If `‖z‖ ≤ 2 re z + 12 E²` and `‖z‖ ≤ G²` with `E, G ≥ 0`, then `‖z‖ ≤ 2 re z + 6 E G`: this is
the geometric mean of the bounds `12 E²` and `3 G²` for `‖z‖ - 2 re z`. -/
lemma norm_le_two_mul_re_add_mul {z : ℂ} {E G : ℝ} (hE : 0 ≤ E) (hG : 0 ≤ G)
    (h_cone : ‖z‖ ≤ 2 * z.re + 12 * E ^ 2) (h_decay : ‖z‖ ≤ G ^ 2) :
    ‖z‖ ≤ 2 * z.re + 6 * E * G := by
  by_contra h_gt
  have h_nonneg : 0 ≤ 6 * E * G := by positivity
  have h_sq : (‖z‖ - 2 * z.re) * (‖z‖ - 2 * z.re) ≤ 12 * E ^ 2 * (3 * G ^ 2) :=
    mul_le_mul (by linarith) (by linarith [neg_le_of_abs_le (abs_re_le_norm z)]) (by linarith)
      (by positivity)
  linarith [mul_self_lt_mul_self h_nonneg (by linarith : 6 * E * G < ‖z‖ - 2 * z.re)]

/-- **The cone with a decaying error.** Let `j` and `φ` satisfy `IsLaplaceDatum` with `B ≥ 1`. Let
the entries of `l` and `k` be bounded by `L`, let `log β ≥ 1` and `card n + card m + L ≤ β`, and put
`N = (card n + card m)²`. Let both doubled parameters have gap `500 · (dimension)³ + h`, with
`h ≥ 10³⁰ (N log β)³`. Write `j s = (g, g')` and `z` for the value at `s` of `laplaceIntegrand`.
Then `‖z‖ ≤ 2 re z + 6 β ^ (-50 N) (2 / ‖g ⊕ g'‖) ^ (9 N)`. -/
lemma IsLaplaceDatum.norm_laplaceIntegrand_le_two_mul_re_add_mul_pow
    (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hl : l.HasLargeGap h) (hk : k.HasLargeGap h) (hB : 1 ≤ B) (hl_le : ∀ a : n, |l a| ≤ L)
    (hk_le : ∀ a : m, |k a| ≤ L) (hβ_le : card n + card m + L ≤ β) (hβ : 1 ≤ β.log)
    (hh : 10 ^ 30 * ((card n + card m) ^ 2 * β.log) ^ 3 ≤ h) (s : S) :
    ‖l.laplaceIntegrand k j φ s‖ ≤ 2 * (l.laplaceIntegrand k j φ s).re +
      6 * β⁻¹ ^ (50 * (card n + card m) ^ 2) *
        (2 / ‖(U.sum (signMatrix_sum ε η) (j s) : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖) ^
          (9 * (card n + card m) ^ 2) := by
  -- Combine the constant error of the cone with the decay `‖z‖ ≤ (2 / ‖g ⊕ g'‖) ^ (18 N)`.
  set N : ℕ := (card n + card m) ^ 2 with hN
  have hN_cast : (N : ℝ) = (card n + card m) ^ 2 := by simp [hN]
  have hβ_pos : 0 < β := lt_of_lt_of_le (by positivity) hβ_le
  have h_gap : 18 * N ≤ h := eighteen_mul_le_of_mul_pow_three_le
    (Nat.one_le_pow _ _ (Nat.add_pos_left card_pos _)) hβ (by rwa [hN_cast])
  have h_err : rexp (-100 * ((card n + card m : ℝ) ^ 2 * β.log)) = (β⁻¹ ^ (50 * N)) ^ 2 := by
    rw [← hN_cast, ← pow_mul, ← exp_log (inv_pos.2 hβ_pos), ← Real.exp_natCast_mul, Real.log_inv]
    push_cast
    ring_nf
  have h_cone : ‖l.laplaceIntegrand k j φ s‖ ≤
      2 * (l.laplaceIntegrand k j φ s).re + 12 * (β⁻¹ ^ (50 * N)) ^ 2 :=
    (h_datum.norm_laplaceIntegrand_le_mul_re_add hl hk hB hl_le hk_le hβ_le hβ rfl hh s).trans_eq
      (by rw [h_err])
  have h_decay : ‖l.laplaceIntegrand k j φ s‖ ≤
      ((2 / ‖(U.sum (signMatrix_sum ε η) (j s) : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖) ^ (9 * N)) ^ 2 :=
    (h_datum.norm_laplaceIntegrand_le_pow hl hk (by omega) s).trans_eq (pow_mul _ _ 2)
  exact norm_le_two_mul_re_add_mul (by positivity) (by positivity) h_cone h_decay

/-- **The pointwise bounds.** Let `j` and `φ` satisfy `IsLaplaceDatum` with `B ≥ 1`, let the entries
of `l` and `k` be bounded by `L`, let `β ≥ 3` and `card n + card m + L ≤ β`, put
`N = (card n + card m)²`, and let both parameters have gap `500 · (dimension)³ + h` with
`h ≥ 10³⁰ (N log β)³`. Write `j s = (g, g')`, `G = (2 / ‖g ⊕ g'‖) ^ (9 N)` in the operator norm and
`z` for the value at `s` of `laplaceIntegrand`. Then `‖z‖ ≤ G` and
`‖z‖ ≤ 2 re z + 6 β ^ (-50 N) G`. -/
lemma IsLaplaceDatum.norm_laplaceIntegrand_le_two_mul_re_add
    (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hl : l.HasLargeGap h) (hk : k.HasLargeGap h) (hB : 1 ≤ B) (hl_le : ∀ a : n, |l a| ≤ L)
    (hk_le : ∀ a : m, |k a| ≤ L) (hβ : 3 ≤ β) (hβ_le : card n + card m + L ≤ β)
    (hh : 10 ^ 30 * ((card n + card m) ^ 2 * β.log) ^ 3 ≤ h)
    {N : ℕ} (hN : N = (card n + card m) ^ 2) (s : S) :
    ‖l.laplaceIntegrand k j φ s‖ ≤
      (2 / ‖(U.sum (signMatrix_sum ε η) (j s) : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖) ^ (9 * N) ∧
    ‖l.laplaceIntegrand k j φ s‖ ≤ 2 * (l.laplaceIntegrand k j φ s).re + 6 * β⁻¹ ^ (50 * N) *
      (2 / ‖(U.sum (signMatrix_sum ε η) (j s) : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖) ^ (9 * N) := by
  have h_log : 1 ≤ β.log := (le_log_iff_exp_le (by linarith)).2 (exp_one_lt_three.le.trans hβ)
  subst hN
  have h_gap : 18 * (card n + card m) ^ 2 ≤ h := eighteen_mul_le_of_mul_pow_three_le
    (Nat.one_le_pow _ _ (Nat.add_pos_left card_pos _)) h_log (by simpa using hh)
  exact ⟨h_datum.norm_laplaceIntegrand_le_pow hl hk (by omega) s,
    h_datum.norm_laplaceIntegrand_le_two_mul_re_add_mul_pow hl hk hB hl_le hk_le hβ_le h_log hh s⟩

/-- Integration of the bound `‖f‖ ≤ 2 re f + c G`: if moreover `‖f‖ ≥ 1 / 4` on `A`, then
`ν(A) / 4 ≤ 2 ‖∫ f‖ + c ∫ G`. -/
lemma measureReal_div_four_le {α : Type} [MeasurableSpace α] (ν : Measure α) {f : α → ℂ}
    {G : α → ℝ} {c : ℝ} {A : Set α} (hf : Integrable f ν) (hG : Integrable G ν)
    (h_le : ∀ s : α, ‖f s‖ ≤ 2 * (f s).re + c * G s) (hA : ∀ s ∈ A, 1 / 4 ≤ ‖f s‖) :
    ν.real A / 4 ≤ 2 * ‖∫ s : α, f s ∂ν‖ + c * ∫ s : α, G s ∂ν := by
  have h_re : Integrable (fun s : α ↦ (f s).re) ν := hf.re
  calc ν.real A / 4 ≤ 1 / 4 * ν.real {s : α | 1 / 4 ≤ ‖f s‖} := by
        linarith [(measureReal_mono hA (hf.measure_norm_ge_lt_top (by norm_num)).ne :
          ν.real A ≤ ν.real {s : α | 1 / 4 ≤ ‖f s‖})]
    _ ≤ ∫ s, ‖f s‖ ∂ν :=
        mul_meas_ge_le_integral_of_nonneg (.of_forall fun s ↦ norm_nonneg (f s)) hf.norm (1 / 4)
    _ ≤ ∫ s, 2 * (f s).re + c * G s ∂ν :=
        integral_mono hf.norm ((h_re.const_mul 2).add (hG.const_mul c)) h_le
    _ = 2 * (∫ s, f s ∂ν).re + c * ∫ s, G s ∂ν := by
        rw [integral_add (h_re.const_mul 2) (hG.const_mul c), integral_const_mul,
          integral_const_mul, show ∫ s, (f s).re ∂ν = (∫ s, f s ∂ν).re from integral_re hf]
    _ ≤ 2 * ‖∫ s, f s ∂ν‖ + c * ∫ s, G s ∂ν := by linarith [re_le_norm (∫ s, f s ∂ν)]

variable [MeasurableSpace S] [MeasurableMul S] (ν : Measure S) [ν.IsMulRightInvariant]

/-- The covering bound for two radii, for a right invariant measure `ν` on `S` and the `L²` operator
norm: for `J : S →* U(ζ)` with `ζ` indexed by `ι` and `β ≥ 10¹²`, the volume of `{‖J s‖ ≤ β + 1}` is
at most `β ^ (16 (card ι)²)` times that of `{‖J s - 1‖ ≤ (200 β⁵)⁻¹}`. -/
lemma measure_large_ball_le_pow_mul_small_ball {ι : Type} [Fintype ι] [DecidableEq ι]
    {ζ : ι → ℤˣ} (J : S →* USign ζ) (hβ : 10 ^ 12 ≤ β) :
    ν {s : S | ‖(J s : Matrix ι ι ℂ)‖ ≤ β + 1} ≤ ENNReal.ofReal (β ^ (16 * card ι ^ 2)) *
      ν {s : S | ‖(J s : Matrix ι ι ℂ) - 1‖ ≤ (200 * β ^ 5)⁻¹} := by
  have h_radii : 3 * (200 * β ^ 5) * (β + 1) ^ 2 ≤ β ^ 8 := by
    field_simp
    nlinarith
  have h_one : 1 ≤ 200 * β ^ 5 := by linarith [one_le_pow₀ (n := 5) (by linarith : 1 ≤ β)]
  simpa only [mul_one, ← pow_mul, ← mul_assoc, Nat.reduceMul] using
    measure_ball_le_covering ν J 1 h_one (by linarith) h_radii

/-- **Laplace's method.** Let `j : S →* U(ε) × U(η)` and `φ` satisfy `IsLaplaceDatum` with `B ≥ 1`:
the weight of the lowest `K`-type of `l` is `0` at the indices `e (inl x)`, `x : X`, and decreases
in `[-3 B, -B]` elsewhere, that of `k` is nonnegative and `0` on the image of `τ`, the difference
`φ` of the two phases is additive and imaginary, and the image of `j` contains `U(X)`, placed in the
two factors by `e` and `τ`. Let the first component of `j` be proper and the second continuous, and
let `ν` be a right invariant measure on `S` that is finite on compact sets. Let the entries of the
Harish-Chandra parameters `l = 2λ`, `k` (doubled) be bounded by `L`, let `β ≥ 10¹²` bound
`card n + card m + L`, and let both have gap `500 · (dimension)³ + h` with
`h ≥ 10³⁰ ((card n + card m)² log β)³`. Then the function `θ = laplaceIntegrand` is integrable, and
the volume of the set of `s` at which both components of `j s` have operator norm at most `β + 1` is
at most `β ^ (20 (card n + card m)²) ‖∫ θ‖`. -/
theorem IsLaplaceDatum.laplace_method [TopologicalSpace S] [BorelSpace S]
    [IsFiniteMeasureOnCompacts ν] (h_datum : IsLaplaceDatum l k j τ B e φ)
    (hj : IsProperMap fun s : S ↦ (j s).1) (hj' : Continuous fun s : S ↦ (j s).2)
    (hl : l.HasLargeGap h) (hk : k.HasLargeGap h) (hB : 1 ≤ B) (hl_le : ∀ a : n, |l a| ≤ L)
    (hk_le : ∀ a : m, |k a| ≤ L) (hβ : 10 ^ 12 ≤ β) (hβ_le : card n + card m + L ≤ β)
    (hh : 10 ^ 30 * ((card n + card m) ^ 2 * β.log) ^ 3 ≤ h) :
    Integrable (l.laplaceIntegrand k j φ) ν ∧
    ν {s : S | ‖((j s).1 : Matrix n n ℂ)‖ ≤ β + 1 ∧ ‖((j s).2 : Matrix m m ℂ)‖ ≤ β + 1} ≤
      ENNReal.ofReal (β ^ (20 * (card n + card m) ^ 2) *
        ‖∫ s : S, l.laplaceIntegrand k j φ s ∂ν‖) := by
  -- Integrate the pointwise bounds (cone and decay) along the proper map `J : s ↦ g ⊕ g'`, where
  -- `j s = (g, g')`, and compare the volumes of a large and a small ball by covering.
  have hβ16 : 16 ≤ β := le_trans (by norm_num) hβ
  set N : ℕ := (card n + card m) ^ 2 with hN
  let J : S →* USign (Sum.elim ε η) := (U.sum (signMatrix_sum ε η)).comp j
  have hJ : IsProperMap J := isProperMap_sum hj hj'
  let Large : Set S := {s : S | ‖(J s : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖ ≤ β + 1}
  let UnitBall : Set S := {s | ‖(J s : Matrix (n ⊕ m) (n ⊕ m) ℂ) - 1‖ ≤ 1}
  let Small : Set S := {s : S | ‖(J s : Matrix (n ⊕ m) (n ⊕ m) ℂ) - 1‖ ≤ (200 * β ^ 5)⁻¹}
  let G (s : S) : ℝ := (2 / ‖(J s : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖) ^ (9 * N)
  have h_decay_cone : ∀ s : S, ‖l.laplaceIntegrand k j φ s‖ ≤ G s ∧ ‖l.laplaceIntegrand k j φ s‖ ≤
      2 * (l.laplaceIntegrand k j φ s).re + 6 * β⁻¹ ^ (50 * N) * G s :=
    h_datum.norm_laplaceIntegrand_le_two_mul_re_add hl hk hB hl_le hk_le (by linarith) hβ_le hh hN
  -- The decay makes `laplaceIntegrand` integrable.
  have hN_pos : 1 ≤ N := Nat.one_le_pow _ _ (Nat.add_pos_left card_pos _)
  obtain ⟨hG_int, hG_le⟩ : Integrable G ν ∧ ∫ s, G s ∂ν ≤ 16 ^ (9 * N) * ν.real UnitBall := by
    simpa only [mul_one] using integral_decay_le ν hJ (c := 9 * N) (by rw [card_sum]; omega) 1
  have hθ_cont : Continuous (l.laplaceIntegrand k j φ) := by
    have hj_cont : Continuous fun s : S ↦ (j s).1 := hj.continuous
    obtain rfl : (fun s : S ↦ l.phase k (subOnePair j s)) = φ := funext h_datum.phase_eq
    fun_prop [laplaceIntegrand, phase]
  have hθ_int : Integrable (l.laplaceIntegrand k j φ) ν :=
    hG_int.mono' hθ_cont.aestronglyMeasurable (.of_forall fun s ↦ (h_decay_cone s).1)
  -- The covering bound compares the large ball with the small one, on which the integrand has
  -- norm at least `1 / 4`.
  have h_small_fin : ν Small ≠ ⊤ := measure_ball_ne_top_of_isProperMap ν hJ _
  have h_cover : ν Large ≤ ENNReal.ofReal (β ^ (16 * N)) * ν Small := by
    simpa only [card_sum] using measure_large_ball_le_pow_mul_small_ball ν J hβ
  have h_cover_real : ν.real Large ≤ β ^ (16 * N) * ν.real Small := by
    simpa [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ β ^ (16 * N))] using
      ENNReal.toReal_mono (by finiteness) h_cover
  have h_large_fin : ν Large ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) h_cover
  have h_int : ν.real Small / 4 ≤ 2 * ‖∫ s, l.laplaceIntegrand k j φ s ∂ν‖ +
      6 * β⁻¹ ^ (50 * N) * (16 ^ (9 * N) * ν.real Large) := by
    refine (measureReal_div_four_le ν hθ_int hG_int (fun s ↦ (h_decay_cone s).2) fun s hs ↦
      h_datum.one_div_four_le_norm_laplaceIntegrand hl hk hl_le hk_le hβ_le hs).trans ?_
    grw [hG_le, measureReal_mono (s₁ := UnitBall) (s₂ := Large)
      (fun s hs ↦ (norm_le_norm_add_norm_sub' _ 1).trans (by
        simpa only [norm_one] using add_le_add (show 1 ≤ β by linarith) hs)) h_large_fin]
  refine ⟨hθ_int, (measure_mono fun s hs ↦ ?_).trans <|
    (ENNReal.le_ofReal_iff_toReal_le h_large_fin (by positivity)).2 <|
      le_pow_mul_of_le hβ16 hN_pos measureReal_nonneg (norm_nonneg _) h_cover_real h_int⟩
  simpa [Large, J, norm_coe_sum_eq_max] using hs

end New.DiscreteSeries

end LaplaceMethod

/-!
## Lagrange interpolation weights and codimension-one restriction

For strictly decreasing integer nodes `x 0 > x 1 > … > x (N - 1)`, the derivative of the nodal
polynomial `∏ j, (X - x j)` at `x k` has sign `(-1) ^ k` and modulus at least `1`. Writing its
modulus as `c k ^ 2` with `c k ≥ 1` turns Lagrange's residue formula for the coefficient of
`X ^ (N - 1)` into an alternating sum of values divided by `c k ^ 2`.

Applied to the `(M + 1) + M` non-zero lowest-`K`-type weights of two steep parameters `l` on `U(ε)`
and `-l'` on `U(ε ⊕ 1)` (with `M` even), those weights assemble directly into a signed Cauchy
matrix `ω ∈ U(ε ⊕ 1)` of controlled norm such that `(intDiagonal l.lowestKType ⊕ 0) * ω` and
`ω * intDiagonal l'.lowestKType` differ on the first `n` rows only by a multiple of the last row of
`ω`. Hence `j g = (g, ω⁻¹ (g ⊕ 1) ω)` satisfies `IsLaplaceDatum` directly with phase `0`, without
passing through any auxiliary flag-lowering subgroup.
-/

section RestrictionPeriod

open Polynomial Finset Lagrange Matrix Complex MeasureTheory ComplexConjugate New.HCParam

namespace New.DiscreteSeries

/-- **Lagrange interpolation weights for decreasing integer nodes.** Given strictly decreasing
integers `x 0 > x 1 > … > x (N - 1)`, there are real weights `c k ≥ 1` with
`c k ^ 2 = (-1) ^ k * ∏_{j ≠ k} (x k - x j)` such that every real polynomial `P` of degree below
`N` has `(N - 1)`-st coefficient `∑ k, (-1) ^ k * (P.eval (x k) / c k ^ 2)`. -/
lemma exists_lagrange_weights {N : ℕ} {x : Fin N → ℤ} (hx : StrictAnti x) :
    ∃ c : Fin N → ℝ,
      (∀ k : Fin N, 1 ≤ c k ∧ c k ^ 2 = (-1) ^ k.val * ∏ j ∈ univ.erase k, (x k - x j : ℝ)) ∧
      ∀ P : ℝ[X], P.degree < N →
        P.coeff (N - 1) = ∑ k : Fin N, (-1) ^ k.val * (P.eval (x k : ℝ) / c k ^ 2) := by
  have h_prod_int (k : Fin N) : 1 ≤ (-1 : ℤ) ^ k.val * ∏ j ∈ univ.erase k, (x k - x j) := by
    -- Factors with `j > k` are positive (`x k - x j ≥ 1`), and the `k` factors with `j < k`
    -- contribute `(-1) ^ k` times positive differences `x j - x k ≥ 1`.
    have h_split : (-1 : ℤ) ^ k.val * ∏ j ∈ univ.erase k, (x k - x j) =
        (∏ j ∈ Ioi k, (x k - x j)) * ∏ j ∈ Iio k, (x j - x k) := by
      rw [← compl_singleton, ← Ioi_disjUnion_Iio, prod_disjUnion (disjoint_Ioi_Iio k),
        ← Fin.card_Iio, mul_left_comm, ← prod_neg]
      simp_rw [neg_sub]
    rw [h_split]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_prod₀ fun j hj ↦ Int.sub_pos.2 (hx (mem_Ioi.1 hj)))
      (one_le_prod₀ fun j hj ↦ Int.sub_pos.2 (hx (mem_Iio.1 hj)))
  have h_prod (k : Fin N) : 1 ≤ (-1 : ℝ) ^ k.val * ∏ j ∈ univ.erase k, (x k - x j : ℝ) := by
    exact_mod_cast h_prod_int k
  let c (k : Fin N) : ℝ := √((-1 : ℝ) ^ k.val * ∏ j ∈ univ.erase k, (x k - x j : ℝ))
  have hc (k : Fin N) : 1 ≤ c k ∧ c k ^ 2 = (-1) ^ k.val * ∏ j ∈ univ.erase k, (x k - x j : ℝ) :=
    ⟨Real.one_le_sqrt.2 (h_prod k), Real.sq_sqrt (zero_le_one.trans (h_prod k))⟩
  refine ⟨c, hc, fun P hP ↦ ?_⟩
  have h_inj : Set.InjOn (fun k : Fin N ↦ (x k : ℝ)) (univ : Finset (Fin N)) :=
    (Int.cast_injective.comp hx.injective).injOn
  have h_eq := coeff_eq_sum h_inj (by simpa only [Finset.card_fin] using hP)
  rw [Finset.card_fin] at h_eq
  rw [h_eq]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [(hc k).2, ← mul_div_assoc, mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num))]

/-- If `x : Fin N → ℤ` is strictly decreasing with `|x i - x j| ≤ D` (`1 ≤ D`) and `c y ^ 2` equals
`|∏_{z ≠ y} (x y - x z)|`, then for any injective index map `g : ι → Fin N` and `s : Finset ι`,
`((∏ j ∈ s, (x y - x (g j))) / c y) ^ 2 ≤ D ^ #s`. Either `y` occurs in `g '' s` and the product
vanishes, or `s.map ⟨g, hg⟩ ⊆ univ.erase y` and all remaining integer differences in `c y ^ 2` have
modulus at least `1`. -/
lemma sq_prod_sub_div_le_pow {N : ℕ} {ι : Type*} [DecidableEq ι] {x : Fin N → ℤ} {c : Fin N → ℝ}
    {D : ℝ} (hx : StrictAnti x) (hD_one : 1 ≤ D) (hD : ∀ i j : Fin N, |(x i - x j : ℝ)| ≤ D)
    (hc : ∀ y : Fin N, 1 ≤ c y ∧ c y ^ 2 = (-1) ^ y.val * ∏ z ∈ univ.erase y, (x y - x z : ℝ))
    {g : ι → Fin N} (hg : Function.Injective g) (s : Finset ι) (y : Fin N) :
    ((∏ j ∈ s, (x y - x (g j) : ℝ)) / c y) ^ 2 ≤ D ^ #s := by
  by_cases hy : ∃ j ∈ s, g j = y
  · obtain ⟨j, hj, rfl⟩ := hy
    rw [prod_eq_zero hj (sub_self _), zero_div, sq, mul_zero]
    positivity
  · push Not at hy
    have h_sub : s.map ⟨g, hg⟩ ⊆ univ.erase y := fun z hz ↦ by
      obtain ⟨j, hj, rfl⟩ := mem_map.1 hz
      exact mem_erase.2 ⟨hy j hj, mem_univ _⟩
    have h_one_le (z : Fin N) (hz : z ∈ univ.erase y) : 1 ≤ |(x y - x z : ℝ)| := by
      have hne : y ≠ z := (mem_erase.1 hz).1.symm
      exact_mod_cast Int.one_le_abs (sub_ne_zero.2 (hx.injective.ne hne))
    have hc_abs : c y ^ 2 = ∏ z ∈ univ.erase y, |(x y - x z : ℝ)| :=
      calc c y ^ 2 = |c y ^ 2| := (abs_of_nonneg (sq_nonneg _)).symm
        _ = |(-1 : ℝ) ^ y.val * ∏ z ∈ univ.erase y, (x y - x z : ℝ)| := by rw [(hc y).2]
        _ = ∏ z ∈ univ.erase y, |(x y - x z : ℝ)| := by simp [abs_mul, abs_prod]
    have h_le_cy : ∏ j ∈ s, |(x y - x (g j) : ℝ)| ≤ c y ^ 2 := by
      rw [hc_abs, ← prod_sdiff h_sub, prod_map s ⟨g, hg⟩ fun z ↦ |(x y - x z : ℝ)|]
      exact le_mul_of_one_le_left (prod_nonneg fun _ _ ↦ abs_nonneg _)
        (one_le_prod₀ fun z hz ↦ h_one_le z (sdiff_subset hz))
    have h_le_D : ∏ j ∈ s, |(x y - x (g j) : ℝ)| ≤ D ^ #s :=
      (prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun j _ ↦ hD y (g j)).trans_eq (prod_const D)
    have hc_pos : 0 < c y ^ 2 := by linarith [(hc y).1, sq_nonneg (c y - 1)]
    rw [div_pow, ← sq_abs (∏ j ∈ s, _), abs_prod, div_le_iff₀ hc_pos]
    calc (∏ j ∈ s, |(x y - x (g j) : ℝ)|) ^ 2
        = (∏ j ∈ s, |(x y - x (g j) : ℝ)|) * ∏ j ∈ s, |(x y - x (g j) : ℝ)| := sq _
      _ ≤ D ^ #s * c y ^ 2 := mul_le_mul h_le_D h_le_cy (prod_nonneg fun _ _ ↦ abs_nonneg _)
          (pow_nonneg (zero_le_one.trans hD_one) _)

/-- **Direct Laplace datum for codimension-one restriction.** Let `l` on `U(ε)` and `-l'` on
`U(ε ⊕ 1)` satisfy `IsSteep` with respect to `B ≥ 1` and coordinate splittings `e : X ⊕ Fin M ≃ n`
and `e' : X ⊕ Fin (M + 1) ≃ n ⊕ Unit`, where `M` is even and `l'` has distinct entries (`HasGap`).
Then there is a signed Cauchy matrix `ω ∈ U(ε ⊕ 1)` with entries bounded in norm by
`(6 B) ^ (M + 1)` such that `j g = (g, ω⁻¹ (g ⊕ 1) ω)` satisfies
`IsLaplaceDatum l l' j (e' ∘ Sum.inl) B e 0` with zero phase. -/
lemma IsSteep.exists_isLaplaceDatum_restriction {n X : Type} [Fintype n] [DecidableEq n]
    [Fintype X] [DecidableEq X] {ε : n → ℤˣ} {B : ℝ} {h M : ℕ} {l : HCParam ε}
    {l' : HCParam (Sum.elim ε (1 : Unit → ℤˣ))} {e : X ⊕ Fin M ≃ n}
    {e' : X ⊕ Fin (M + 1) ≃ n ⊕ Unit} (hM : Even M) (h_steep : IsSteep l B e)
    (h_steep' : IsSteep (-l') B e') (hl'_gap : l'.HasGap h) (hB : 1 ≤ B) :
    ∃ ω : USign (Sum.elim ε (1 : Unit → ℤˣ)),
      let j : USign ε →* USign ε × USign (Sum.elim ε (1 : Unit → ℤˣ)) :=
        (MonoidHom.id (USign ε)).prod ((MulAut.conj ω).symm.toMonoidHom.comp (U.inl ε 1))
      (∀ i j : n ⊕ Unit, ‖(ω : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) i j‖ ≤ (6 * B) ^ (M + 1)) ∧
      IsLaplaceDatum l l' j (e' ∘ Sum.inl) B e 0 ∧
      ∀ g : USign ε, (subOnePair j g).2 =
        (↑ω⁻¹ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) *
          fromBlocks ((g : Matrix n n ℂ) - 1) 0 0 0 * (ω : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) := by
  have h_ktype' : (-l').lowestKType = -l'.lowestKType := lowestKType_neg hl'_gap
  -- Concatenate the `M + 1` positive weights of `l'` (in decreasing order) with the `M` negative
  -- weights of `l`.
  let x : Fin ((M + 1) + M) → ℤ :=
    Fin.append (fun a : Fin (M + 1) ↦ l'.lowestKType (e' (.inr a.rev)))
      (fun k : Fin M ↦ l.lowestKType (e (.inr k)))
  have hx_pos (a : Fin (M + 1)) : (l'.lowestKType (e' (.inr a)) : ℝ) ∈ Set.Icc B (3 * B) := by
    have h_mem := h_steep'.weight_mem a
    rw [h_ktype', Pi.neg_apply, Int.cast_neg] at h_mem
    exact ⟨by linarith [h_mem.2], by linarith [h_mem.1]⟩
  have hx_anti_left : StrictAnti fun a : Fin (M + 1) ↦ l'.lowestKType (e' (.inr a.rev)) := by
    intro a₁ a₂ ha
    have h_lt : (-l').lowestKType (e' (.inr a₁.rev)) < (-l').lowestKType (e' (.inr a₂.rev)) :=
      h_steep'.weight_strictAnti (Fin.rev_lt_rev.2 ha)
    rw [h_ktype', Pi.neg_apply, Pi.neg_apply] at h_lt
    linarith
  have hx : StrictAnti x := by
    rw [StrictAnti, Fin.forall_fin_add]
    refine ⟨fun a₁ ↦ ?_, fun k₁ ↦ ?_⟩
    · rw [Fin.forall_fin_add]
      refine ⟨fun a₂ hij ↦ ?_, fun k₂ _ ↦ ?_⟩
      · simp only [x, Fin.append_left]
        exact hx_anti_left (Fin.lt_def.2 (by simpa only [Fin.lt_def, Fin.val_castAdd] using hij))
      · simp only [x, Fin.append_left, Fin.append_right]
        exact_mod_cast (by linarith [(h_steep.weight_mem k₂).2, (hx_pos a₁.rev).1] :
          (l.lowestKType (e (.inr k₂)) : ℝ) < l'.lowestKType (e' (.inr a₁.rev)))
    · rw [Fin.forall_fin_add]
      refine ⟨fun a₂ hij ↦ ?_, fun k₂ hij ↦ ?_⟩
      · exfalso
        simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at hij
        omega
      · simp only [x, Fin.append_right]
        exact h_steep.weight_strictAnti
          (Fin.lt_def.2 (by simp only [Fin.lt_def, Fin.val_natAdd] at hij; omega))
  have hx_abs : ∀ y : Fin ((M + 1) + M), |(x y : ℝ)| ≤ 3 * B := by
    rw [Fin.forall_fin_add]
    exact ⟨fun a ↦ by
      simp only [x, Fin.append_left]
      exact abs_le.2 ⟨by linarith [(hx_pos a.rev).1], (hx_pos a.rev).2⟩, fun k ↦ by
      simp only [x, Fin.append_right]
      exact abs_le.2
        ⟨by linarith [(h_steep.weight_mem k).1], by linarith [(h_steep.weight_mem k).2]⟩⟩
  have hx_diff (y z : Fin ((M + 1) + M)) : |(x y - x z : ℝ)| ≤ 6 * B :=
    (abs_sub _ _).trans (by linarith [hx_abs y, hx_abs z])
  obtain ⟨c, hc, h_lagrange⟩ := exists_lagrange_weights hx
  -- Build the Cauchy entries `R` and the bottom row `d` from the Lagrange weights `c`.
  let d (a : Fin (M + 1)) : ℝ :=
    (-1) ^ a.val * ((∏ k : Fin M, (x (Fin.castAdd M a) - x (Fin.natAdd (M + 1) k) : ℝ)) /
      c (Fin.castAdd M a))
  let R (y : Fin ((M + 1) + M)) (a : Fin (M + 1)) : ℝ :=
    d a * ((∏ b ∈ univ.erase a, (x y - x (Fin.castAdd M b) : ℝ)) / c y)
  have hR_cast (a b : Fin (M + 1)) : R (Fin.castAdd M b) a = if a = b then 1 else 0 := by
    rcases eq_or_ne a b with rfl | hab
    · rw [ite_eq_left rfl]
      have h_split : ∏ z ∈ univ.erase (Fin.castAdd M a), (x (Fin.castAdd M a) - x z : ℝ) =
          (∏ b' ∈ univ.erase a, (x (Fin.castAdd M a) - x (Fin.castAdd M b') : ℝ)) *
            ∏ k : Fin M, (x (Fin.castAdd M a) - x (Fin.natAdd (M + 1) k) : ℝ) := by
        simp only [← filter_ne', prod_filter]
        rw [Fin.prod_univ_add]
        congr 1
        · exact prod_congr rfl fun b' _ ↦ by simp
        · exact prod_congr rfl fun k _ ↦ by
            simp [show Fin.natAdd (M + 1) k ≠ Fin.castAdd M a by
              simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]; omega]
      have hc_sq : c (Fin.castAdd M a) ^ 2 =
          (-1) ^ a.val * ∏ z ∈ univ.erase (Fin.castAdd M a), (x (Fin.castAdd M a) - x z : ℝ) := by
        simpa [Fin.val_castAdd] using (hc (Fin.castAdd M a)).2
      rw [show R (Fin.castAdd M a) a = ((-1) ^ a.val *
            ((∏ b' ∈ univ.erase a, (x (Fin.castAdd M a) - x (Fin.castAdd M b') : ℝ)) *
              ∏ k : Fin M, (x (Fin.castAdd M a) - x (Fin.natAdd (M + 1) k) : ℝ))) /
            c (Fin.castAdd M a) ^ 2 by simp only [R, d]; ring,
        ← h_split, ← hc_sq, div_self (pow_ne_zero 2 (by linarith [(hc (Fin.castAdd M a)).1]))]
    · simp only [ite_eq_right hab, R]
      rw [prod_eq_zero (mem_erase.2 ⟨hab.symm, mem_univ b⟩) (sub_self _), zero_div, mul_zero]
  -- By Lagrange's formula on a monic product of degree `2 M = (M + 1) + M - 1`, the columns of `R`
  -- satisfy the signed orthogonality relation; since `M` is even, the signs match `ε ⊕ 1`.
  have hR_gram (b₁ b₂ : Fin (M + 1)) :
      (∑ k : Fin M, (-1 : ℝ) ^ k.val * (R (Fin.natAdd (M + 1) k) b₁ *
        R (Fin.natAdd (M + 1) k) b₂)) + d b₁ * d b₂ =
        if b₁ = b₂ then (-1) ^ b₁.val else 0 := by
    let P₁ : ℝ[X] := nodal (univ.erase b₁) fun b : Fin (M + 1) ↦ (x (Fin.castAdd M b) : ℝ)
    let P₂ : ℝ[X] := nodal (univ.erase b₂) fun b : Fin (M + 1) ↦ (x (Fin.castAdd M b) : ℝ)
    have hP_deg : (P₁ * P₂).natDegree = 2 * M := by
      rw [nodal_monic.natDegree_mul nodal_monic, natDegree_nodal, natDegree_nodal,
        card_erase_of_mem (mem_univ b₁), card_erase_of_mem (mem_univ b₂), Finset.card_fin,
        add_tsub_cancel_right, two_mul]
    have h_coeff : (P₁ * P₂).coeff ((M + 1) + M - 1) = 1 := by
      rw [show (M + 1) + M - 1 = (P₁ * P₂).natDegree by omega,
        (nodal_monic.mul nodal_monic).coeff_natDegree]
    have h_res := congrArg (d b₁ * d b₂ * ·) (h_coeff.symm.trans (h_lagrange (P₁ * P₂)
      (degree_le_natDegree.trans_lt (by rw [hP_deg]; norm_cast; omega))))
    rw [mul_one, mul_sum, sum_congr rfl fun y _ ↦ (by
        simp only [P₁, P₂, eval_mul, eval_nodal, R]; ring :
          d b₁ * d b₂ * ((-1) ^ y.val * ((P₁ * P₂).eval (x y : ℝ) / c y ^ 2)) =
            (-1) ^ y.val * (R y b₁ * R y b₂)), Fin.sum_univ_add] at h_res
    have h_first : ∑ b : Fin (M + 1), (-1 : ℝ) ^ (Fin.castAdd M b).val *
        (R (Fin.castAdd M b) b₁ * R (Fin.castAdd M b) b₂) =
          if b₁ = b₂ then (-1) ^ b₁.val else 0 := by
      simp only [Fin.val_castAdd, hR_cast]
      rcases eq_or_ne b₁ b₂ with rfl | hb
      · simp
      · simp only [hb, ↓reduceIte]
        exact sum_eq_zero fun b _ ↦ by rcases eq_or_ne b₁ b with rfl | h₁ <;> simp [*, hb.symm]
    have h_second : ∑ k : Fin M, (-1 : ℝ) ^ (Fin.natAdd (M + 1) k).val *
        (R (Fin.natAdd (M + 1) k) b₁ * R (Fin.natAdd (M + 1) k) b₂) =
          -∑ k : Fin M, (-1 : ℝ) ^ k.val *
            (R (Fin.natAdd (M + 1) k) b₁ * R (Fin.natAdd (M + 1) k) b₂) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun k _ ↦ by
        rw [Fin.val_natAdd, pow_add, pow_add, hM.neg_one_pow]; ring
    linarith [h_res, h_first, h_second]
  -- Assemble `ω` on `n ⊕ Unit` by placing `1` on `X`, the Cauchy block `R` on
  -- `Fin M × Fin (M + 1)`, and `d` in the extra row `Unit`.
  let f : (X ⊕ Fin M) ⊕ Unit ≃ n ⊕ Unit := e.sumCongr (Equiv.refl Unit)
  let W₀ : Matrix ((X ⊕ Fin M) ⊕ Unit) (X ⊕ Fin (M + 1)) ℂ :=
    fromRows
      (fromBlocks 1 0 0 (of fun (k : Fin M) (a : Fin (M + 1)) ↦
        (R (Fin.natAdd (M + 1) k) a.rev : ℂ)))
      (of fun (_ : Unit) (col : X ⊕ Fin (M + 1)) ↦
        col.elim 0 fun a : Fin (M + 1) ↦ (d a.rev : ℂ))
  let W : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ := Matrix.reindex f e' W₀
  have hW_gram : Wᴴ * signMatrix (Sum.elim ε (1 : Unit → ℤˣ)) * W =
      signMatrix (Sum.elim ε (1 : Unit → ℤˣ)) := by
    ext i₁ i₂
    obtain ⟨x₁ | a₁, rfl⟩ := e'.surjective i₁ <;> obtain ⟨x₂ | a₂, rfl⟩ := e'.surjective i₂ <;>
      rw [signMatrix, Matrix.mul_apply, ← f.sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
    · simp [W, W₀, f, mul_diagonal, diagonal_apply, h_steep.sign_inl, h_steep'.sign_inl,
        Matrix.one_apply, eq_comm]
    · simp [W, W₀, f, mul_diagonal]
    · simp [W, W₀, f, mul_diagonal]
    · rw [Fintype.sum_unique (ι := Unit)]
      have h_rev_sign : (-1 : ℝ) ^ a₁.rev.val = (-1 : ℝ) ^ a₁.val :=
        mul_right_cancel₀ (pow_ne_zero a₁.val (by norm_num : (-1 : ℝ) ≠ 0)) (by
          rw [← pow_add, Fin.rev_add_cast, hM.neg_one_pow, ← pow_add, ← two_mul, pow_mul,
            neg_one_sq, one_pow])
      have h_col := congrArg Complex.ofReal (hR_gram a₁.rev a₂.rev)
      simp only [Fin.rev_inj, h_rev_sign, ofReal_add, ofReal_sum, ofReal_mul, ofReal_pow,
        ofReal_neg, ofReal_one, apply_ite Complex.ofReal, ofReal_zero] at h_col
      simp only [mul_diagonal, conjTranspose_apply, W, reindex_apply, submatrix_apply,
        Equiv.symm_apply_apply]
      simp only [W₀, f, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl, Sum.map_inr,
        Sum.elim_inl, Sum.elim_inr, h_steep.sign_inr, Pi.one_apply, Units.val_one,
        Units.val_pow_eq_pow_val, Units.val_neg, Int.cast_one, Int.cast_pow, Int.cast_neg,
        fromRows_apply_inl, fromRows_apply_inr, fromBlocks_apply₁₂, fromBlocks_apply₂₂,
        Matrix.zero_apply, of_apply, star_zero, Complex.star_def, conj_ofReal, zero_mul, mul_zero,
        sum_const_zero, zero_add, diagonal_apply, e'.injective.eq_iff, Sum.inr.injEq,
        h_steep'.sign_inr]
      rw [← h_col]
      exact congrArg₂ (· + ·) (sum_congr rfl fun k _ ↦ by ring) (by ring)
  let ω : USign (Sum.elim ε (1 : Unit → ℤˣ)) := U.of IsHermitianInvolution.isUnit W hW_gram
  have hω_val : (ω : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) = W := rfl
  have h_inv_W : (↑ω⁻¹ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) * W = 1 := ω.val.inv_val
  have hW_inv : W * (↑ω⁻¹ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) = 1 := ω.val.val_inv
  -- Bound the entries of `ω` by `(6 B) ^ (M + 1)` using `sq_prod_sub_div_le_pow`.
  have h6B : 1 ≤ 6 * B := by linarith
  have hd_sq (a : Fin (M + 1)) : d a ^ 2 ≤ (6 * B) ^ M := by
    have h_sq := sq_prod_sub_div_le_pow hx h6B hx_diff hc (Fin.natAdd_injective M (M + 1))
      univ (Fin.castAdd M a)
    have h_sign : ((-1 : ℝ) ^ a.val) ^ 2 = 1 := by rw [← pow_mul, mul_comm]; simp
    simpa [d, mul_pow, h_sign, Finset.card_fin] using h_sq
  have hd_le (a : Fin (M + 1)) : |d a| ≤ (6 * B) ^ (M + 1) :=
    abs_le_of_sq_le_sq ((hd_sq a).trans ((pow_le_pow_right₀ h6B (Nat.le_succ M)).trans
      (le_self_pow₀ (one_le_pow₀ h6B) two_ne_zero))) (by positivity)
  have hR_le (k : Fin M) (a : Fin (M + 1)) : |R (Fin.natAdd (M + 1) k) a| ≤ (6 * B) ^ (M + 1) := by
    have h_fac := sq_prod_sub_div_le_pow hx h6B hx_diff hc (Fin.castAdd_injective (M + 1) M)
      (univ.erase a) (Fin.natAdd (M + 1) k)
    rw [card_erase_of_mem (mem_univ a), Finset.card_fin, add_tsub_cancel_right] at h_fac
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    rw [show R (Fin.natAdd (M + 1) k) a ^ 2 = d a ^ 2 * _ ^ 2 from mul_pow _ _ 2]
    exact (mul_le_mul (hd_sq a) h_fac (sq_nonneg _) (by positivity)).trans
      ((sq ((6 * B) ^ M)).symm.trans_le (pow_le_pow_left₀ (by positivity)
        (pow_le_pow_right₀ h6B (Nat.le_succ M)) 2))
  have hW_entry (i j : n ⊕ Unit) : ‖W i j‖ ≤ (6 * B) ^ (M + 1) := by
    obtain ⟨(x₁ | k₁) | ⟨⟩, rfl⟩ := f.surjective i <;> obtain ⟨x₂ | a₂, rfl⟩ := e'.surjective j <;>
      simp only [W, W₀, reindex_apply, submatrix_apply, Equiv.symm_apply_apply, fromRows_apply_inl,
        fromRows_apply_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply, of_apply, Sum.elim_inl,
        Sum.elim_inr, Pi.zero_apply]
    · split_ifs <;> simp [one_le_pow₀ h6B, pow_nonneg (zero_le_one.trans h6B)]
    · simp [pow_nonneg (zero_le_one.trans h6B)]
    · simp [pow_nonneg (zero_le_one.trans h6B)]
    · simpa using hR_le k₁ a₂.rev
    · simp [pow_nonneg (zero_le_one.trans h6B)]
    · simpa using hd_le a₂.rev
  let j : USign ε →* USign ε × USign (Sum.elim ε (1 : Unit → ℤˣ)) :=
    (MonoidHom.id (USign ε)).prod ((MulAut.conj ω).symm.toMonoidHom.comp (U.inl ε 1))
  have hj_snd (g : USign ε) : (subOnePair j g).2 =
      (↑ω⁻¹ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) *
        fromBlocks ((g : Matrix n n ℂ) - 1) 0 0 0 * W := by
    have h_inl : (U.inl ε (1 : Unit → ℤˣ) g : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1 =
        fromBlocks ((g : Matrix n n ℂ) - 1) 0 0 0 := by
      ext (a | a) (b | b) <;> simp [Matrix.one_apply]
    calc ((ω⁻¹ * U.inl ε 1 g * ω : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1
        = (↑ω⁻¹ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) *
            (U.inl ε (1 : Unit → ℤˣ) g : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) * W -
            (↑ω⁻¹ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) * W := by
          rw [h_inv_W]; rfl
      _ = (↑ω⁻¹ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) *
            ((U.inl ε (1 : Unit → ℤˣ) g : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1) * W := by
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      _ = _ := by rw [h_inl]
  -- On the first `n` rows, `W * diag(μ_{l'})` equals `diag(μ_l) * W` plus a rank-one term along
  -- the bottom row of `W`. Multiplying by `ω⁻¹` on the right shows that the upper-left `n × n`
  -- block of `W * diag(μ_{l'}) * ω⁻¹` is `diag(μ_l)`, so the two phases cancel identically.
  have hl'_zero (x₀ : X) : l'.lowestKType (e' (.inl x₀)) = 0 := by
    have hz := h_steep'.weight_eq_zero x₀
    rw [h_ktype', Pi.neg_apply, neg_eq_zero] at hz
    exact hz
  let v (i : n) : ℂ :=
    (e.symm i).elim 0 fun k : Fin M ↦
      -(((∏ b : Fin (M + 1), (x (Fin.natAdd (M + 1) k) - x (Fin.castAdd M b) : ℝ)) /
        c (Fin.natAdd (M + 1) k) : ℝ) : ℂ)
  have h_comm_top : (W * intDiagonal l'.lowestKType).submatrix Sum.inl id =
      fromCols (intDiagonal l.lowestKType) (replicateCol Unit v) * W := by
    ext i col
    rw [submatrix_apply, id_eq, mul_diagonal, Matrix.mul_apply, Fintype.sum_sum_type,
      sum_eq_single i
        (fun i' _ hi' ↦ by simp [fromCols_apply_inl, diagonal_apply_ne' _ hi'])
        (fun h_abs ↦ absurd (mem_univ _) h_abs),
      Fintype.sum_unique]
    obtain ⟨x₁ | k₁, rfl⟩ := e.surjective i <;> obtain ⟨x₂ | a₂, rfl⟩ := e'.surjective col
    · simp [W, W₀, f, v, h_steep.weight_eq_zero, hl'_zero]
    · simp [W, W₀, f, v, h_steep.weight_eq_zero]
    · simp [W, W₀, f, v, hl'_zero]
    · have h_prod_era : (x (Fin.natAdd (M + 1) k₁) - x (Fin.castAdd M a₂.rev) : ℝ) *
          ∏ b ∈ univ.erase a₂.rev, (x (Fin.natAdd (M + 1) k₁) - x (Fin.castAdd M b) : ℝ) =
            ∏ b : Fin (M + 1), (x (Fin.natAdd (M + 1) k₁) - x (Fin.castAdd M b) : ℝ) :=
        mul_prod_erase univ (fun b : Fin (M + 1) ↦
          (x (Fin.natAdd (M + 1) k₁) - x (Fin.castAdd M b) : ℝ)) (mem_univ a₂.rev)
      have h_cauchy : R (Fin.natAdd (M + 1) k₁) a₂.rev * (x (Fin.castAdd M a₂.rev) : ℝ) =
          (x (Fin.natAdd (M + 1) k₁) : ℝ) * R (Fin.natAdd (M + 1) k₁) a₂.rev -
            ((∏ b : Fin (M + 1), (x (Fin.natAdd (M + 1) k₁) - x (Fin.castAdd M b) : ℝ)) /
              c (Fin.natAdd (M + 1) k₁)) * d a₂.rev := by
        simp only [R, ← h_prod_era]
        ring
      have h_lhs : W (Sum.inl (e (.inr k₁))) (e' (.inr a₂)) =
          (R (Fin.natAdd (M + 1) k₁) a₂.rev : ℂ) := by simp [W, W₀, f]
      have h_bot : W (Sum.inr ()) (e' (.inr a₂)) = (d a₂.rev : ℂ) := by simp [W, W₀, f]
      rw [h_lhs, h_bot, show l'.lowestKType (e' (.inr a₂)) = x (Fin.castAdd M a₂.rev) by simp [x],
        fromCols_apply_inl, intDiagonal, diagonal_apply_eq,
        show l.lowestKType (e (.inr k₁)) = x (Fin.natAdd (M + 1) k₁) by simp [x],
        fromCols_apply_inr, replicateCol_apply]
      simpa [v, sub_eq_add_neg] using congrArg Complex.ofReal h_cauchy
  have h_upper_block :
      (W * intDiagonal l'.lowestKType * (↑ω⁻¹ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)).submatrix
        Sum.inl Sum.inl = intDiagonal l.lowestKType := by
    have h_rows :
        (W * intDiagonal l'.lowestKType * (↑ω⁻¹ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)).submatrix
          Sum.inl id = fromCols (intDiagonal l.lowestKType) (replicateCol Unit v) :=
      calc (W * intDiagonal l'.lowestKType * (↑ω⁻¹ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)).submatrix
            Sum.inl id
          = (W * intDiagonal l'.lowestKType).submatrix Sum.inl id *
              (↑ω⁻¹ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) := rfl
        _ = fromCols (intDiagonal l.lowestKType) (replicateCol Unit v) *
              (W * (↑ω⁻¹ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)) := by rw [h_comm_top, Matrix.mul_assoc]
        _ = fromCols (intDiagonal l.lowestKType) (replicateCol Unit v) := by
            rw [hW_inv, Matrix.mul_one]
    ext i₁ i₂
    exact congrFun₂ h_rows i₁ (Sum.inl i₂)
  refine ⟨ω, hW_entry,
    { toIsSteep := h_steep
      phase_eq := fun g ↦ ?_
      trace_eq := fun g ↦ ?_
      phase_mul := fun _ _ ↦ by simp
      re_phase_eq_zero := fun _ ↦ by simp
      sign_weight_right := fun x₀ ↦ ⟨h_steep'.sign_inl x₀, hl'_zero x₀⟩
      weight_nonneg_and_le := fun i _ ↦ ?_
      exists_diagonal := fun u hu ↦ ?_ }, hj_snd⟩
  · have h_tr : (intDiagonal l'.lowestKType * (subOnePair j g).2).trace =
        (intDiagonal l.lowestKType * ((g : Matrix n n ℂ) - 1)).trace :=
      calc (intDiagonal l'.lowestKType * (subOnePair j g).2).trace
          = ((W * intDiagonal l'.lowestKType * (↑ω⁻¹ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)) *
              fromBlocks ((g : Matrix n n ℂ) - 1) 0 0 0).trace := by
            rw [hj_snd, ← Matrix.mul_assoc (intDiagonal l'.lowestKType),
              trace_mul_cycle (intDiagonal l'.lowestKType),
              ← Matrix.mul_assoc (W * intDiagonal l'.lowestKType)]
        _ = ((W * intDiagonal l'.lowestKType * (↑ω⁻¹ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)).submatrix
              Sum.inl Sum.inl * ((g : Matrix n n ℂ) - 1)).trace := by
            simp [trace, Matrix.mul_apply, Fintype.sum_sum_type]
        _ = (intDiagonal l.lowestKType * ((g : Matrix n n ℂ) - 1)).trace := by
            rw [h_upper_block]
    rw [phase, h_tr]
    simp
  · rw [hj_snd, trace_mul_cycle, hW_inv, Matrix.one_mul]
    simp [trace, Fintype.sum_sum_type]
  · obtain ⟨x₀ | a₀, rfl⟩ := e'.surjective i
    · simp [hl'_zero x₀, show (0 : ℝ) ≤ 3 * B by positivity]
    · exact ⟨by exact_mod_cast (zero_le_one.trans hB).trans (hx_pos a₀).1, fun _ ↦ (hx_pos a₀).2⟩
  · obtain ⟨g, hg⟩ := exists_unitary_sub_one_eq_inclMatrix e h_steep.sign_inl
      (mem_unitaryGroup_iff'.1 hu)
    refine ⟨g, Prod.ext hg ?_⟩
    let I₁ : Matrix (n ⊕ Unit) X ℂ := inclMatrix ℂ (Sum.inl ∘ e ∘ Sum.inl)
    let I₂ : Matrix (n ⊕ Unit) X ℂ := inclMatrix ℂ (e' ∘ Sum.inl)
    let Winv : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ := (↑ω⁻¹ : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)
    have h_from : fromBlocks ((g : Matrix n n ℂ) - 1) (0 : Matrix n Unit ℂ)
        (0 : Matrix Unit n ℂ) 0 = I₁ * (u - 1) * I₁ᴴ := by
      rw [hg]
      ext (i₁ | _) (i₂ | _) <;> simp [I₁, inclMatrix, Matrix.mul_apply, Matrix.one_apply]
    have hW_inc : W * I₂ = I₁ := by
      rw [mul_inclMatrix]
      ext i x₀
      obtain ⟨(x₁ | k₁) | ⟨⟩, rfl⟩ := f.surjective i <;>
        simp [I₁, W, W₀, f, inclMatrix, Matrix.one_apply]
    have h_inv_inc : Winv * I₁ = I₂ := by
      rw [← hW_inc, ← Matrix.mul_assoc, h_inv_W, Matrix.one_mul]
    have h_inc_W : I₁ᴴ * W = I₂ᴴ := by
      ext x₀ col
      rw [Matrix.mul_apply]
      obtain ⟨x₂ | a₂, rfl⟩ := e'.surjective col <;>
        simp [I₁, I₂, W, W₀, f, inclMatrix, Matrix.one_apply, eq_comm]
    calc (subOnePair j g).2
        = Winv * (I₁ * (u - 1) * I₁ᴴ) * W := by rw [hj_snd, h_from]
      _ = (Winv * I₁) * (u - 1) * (I₁ᴴ * W) := by simp only [Matrix.mul_assoc]
      _ = I₂ * (u - 1) * I₂ᴴ := by rw [h_inv_inc, h_inc_W]

open Norms.L2Operator in
/-- **Restriction.** Let the parameter `l = 2 λ` of `U(ε)` be steep for `(X, M, B)` with `M` even
and `B ≥ 1`, and let `l' = 2 λ'` be a parameter of `U(ε ⊕ 1)` with `-l'` steep for `(X, M + 1, B)`.
With `n = card n`, let `HasLargeGap h` hold for both: the entries of `l` (resp. `l'`) are distinct
and of the parity of `n - 1` (resp. `n`), and two entries of `λ` (resp. `λ'`) at coordinates of
opposite sign differ by at least `500 n³ + h` (resp. `500 (n + 1)³ + h`). Let the entries of `l`,
`l'` be bounded by `L`, let `β ≥ 10¹²` bound `2 n + 1 + L` and `(n + 1)⁴ (6 B) ^ (2 M + 2)`, and let
`h ≥ 10³⁰ ((2 n + 1)² log β)³`.

Then there is `ω` in `U(ε ⊕ 1)` with `‖ω‖² ≤ β` such that `β ^ (20 (2 n + 1)²)` times the modulus
of the integral over `U(ε)` of `l.dsCoeff g * conj (l'.dsCoeff (ω⁻¹ (g ⊕ 1) ω))` is at least the
volume of `{g | ‖g - 1‖ ≤ 1}`. -/
theorem IsSteep.exists_volume_le_mul_norm_integral_dsCoeff {n X : Type} [Fintype n] [DecidableEq n]
    [Fintype X] [Nonempty n] {ε : n → ℤˣ} {B β : ℝ} {l : HCParam ε}
    {l' : HCParam (Sum.elim ε (1 : Unit → ℤˣ))} {M L h : ℕ} {e : X ⊕ Fin M ≃ n}
    {e' : X ⊕ Fin (M + 1) ≃ n ⊕ Unit} (hM : Even M)
    (h_steep : IsSteep l B e) (h_steep' : IsSteep (-l') B e') (hB : 1 ≤ B)
    (hl : l.HasLargeGap h) (hl' : l'.HasLargeGap h)
    (hL : ∀ a : n, |l a| ≤ L) (hL' : ∀ a : n ⊕ Unit, |l' a| ≤ L) (hβ : 10 ^ 12 ≤ β)
    (hn : Fintype.card (n ⊕ Unit) + Fintype.card n + L ≤ β)
    (h_size : Fintype.card (n ⊕ Unit) ^ 4 * (6 * B) ^ (2 * M + 2) ≤ β)
    (hh : 10 ^ 30 * ((Fintype.card (n ⊕ Unit) + Fintype.card n) ^ 2 * β.log) ^ 3 ≤ h) :
    ∃ y : USign (Sum.elim ε (1 : Unit → ℤˣ)),
      ‖(y : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 ≤ β ∧
      volume.real {g : USign ε | ‖(g : Matrix n n ℂ) - 1‖ ≤ 1} ≤
        β ^ (20 * (Fintype.card (n ⊕ Unit) + Fintype.card n) ^ 2) *
          ‖∫ g : USign ε, l.dsCoeff g *
            conj (l'.dsCoeff (y⁻¹ * U.inl ε 1 g * y : USign (Sum.elim ε 1)))‖ := by
  classical
  obtain ⟨ω, hω_entry, h_datum, hj_snd⟩ :=
    h_steep.exists_isLaplaceDatum_restriction hM h_steep' hl' hB
  have hω_le : ‖(ω : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ≤
      Fintype.card (n ⊕ Unit) ^ 2 * (6 * B) ^ (M + 1) := by
    rw [sq]
    exact l2_opNorm_le_of_apply hω_entry
  let j : USign ε →* USign ε × USign (Sum.elim ε (1 : Unit → ℤˣ)) :=
    (MonoidHom.id (USign ε)).prod ((MulAut.conj ω).symm.toMonoidHom.comp (U.inl ε 1))
  have hω_sq : ‖(ω : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 ≤ β :=
    calc ‖(ω : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2
        ≤ (Fintype.card (n ⊕ Unit) ^ 2 * (6 * B) ^ (M + 1)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hω_le 2
      _ = Fintype.card (n ⊕ Unit) ^ 4 * (6 * B) ^ (2 * M + 2) := by ring
      _ ≤ β := h_size
  have hj_cont : Continuous fun g : USign ε ↦ (j g).2 :=
    ((Homeomorph.smul (ConjAct.toConjAct ω⁻¹)).continuous).comp isProperMap_inl.continuous
  have hn' : Fintype.card n + Fintype.card (n ⊕ Unit) + L ≤ β := by linarith
  have hh' : 10 ^ 30 * ((Fintype.card n + Fintype.card (n ⊕ Unit)) ^ 2 * β.log) ^ 3 ≤ h := by
    rw [← Nat.cast_add, Nat.add_comm, Nat.cast_add]
    exact hh
  obtain ⟨-, h_vol⟩ := h_datum.laplace_method volume isProperMap_id hj_cont hl hl' hB hL hL'
    hβ hn' hh'
  -- The unit ball `{‖g - 1‖ ≤ 1}` in `U(ε)` maps into the set where both components have norm
  -- at most `β + 1`, since `‖ω⁻¹ (g ⊕ 1) ω‖ ≤ 1 + ‖ω‖² ≤ β + 1`.
  have h_ball : {g : USign ε | ‖(g : Matrix n n ℂ) - 1‖ ≤ 1} ⊆
      {g : USign ε | ‖((j g).1 : Matrix n n ℂ)‖ ≤ β + 1 ∧
        ‖((j g).2 : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ≤ β + 1} := fun g hg ↦ by
    have hβ_one : 1 ≤ β := le_trans (by norm_num) hβ
    have hg_norm : ‖(g : Matrix n n ℂ) - 1‖ ≤ 1 := hg
    refine ⟨(norm_le_norm_add_norm_sub' (g : Matrix n n ℂ) 1).trans (by rw [norm_one]; linarith),
      ?_⟩
    rw [eq_add_of_sub_eq' (hj_snd g)]
    have hY : ‖(fromBlocks ((g : Matrix n n ℂ) - 1) 0 0 0 :
        Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ≤ 1 := by
      rwa [norm_fromBlocks_zero_zero, norm_zero, max_eq_left (norm_nonneg _)]
    grw [norm_add_le, norm_one, norm_mul₃_le, U.norm_inv ω, hY, mul_one, ← sq]
    linarith [hω_sq]
  refine ⟨ω, hω_sq, ENNReal.toReal_le_of_le_ofReal (by positivity) ?_⟩
  rw [Nat.add_comm (Fintype.card (n ⊕ Unit))]
  simpa [laplaceIntegrand, j] using (measure_mono h_ball).trans h_vol

end New.DiscreteSeries

end RestrictionPeriod
