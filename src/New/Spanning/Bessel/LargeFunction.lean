module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import TauCeti.Topology.Algebra.Group.Units
import TauCeti.Topology.Instances.Matrix
public import New.Appendix.DiscreteSeries.Periods
public import New.Spanning.Bessel.Average
public import New.Spanning.Bessel.Basic
import Lib.DiscreteSeries.Bessel.SchurBound
import Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure
import Lib.DiscreteSeries.FlenstedJensen.PsiKTypes
import Lib.DiscreteSeries.FlenstedJensen.SquareIntegrability
import Lib.DiscreteSeries.Haar.TotalMass
import Lib.Shimura.Uniformisation.HolomorphicFamilies

/-!
# Bessel systems of discrete series type and a Bessel function large at a point

Given a unitary frame that diagonalises the form `New.Shape.J₁`,
`New.Filling.IsDiscreteSeriesBessel` ties an abstract Bessel system `New.BesselSystem` to a discrete
series parameter `l` and a weight `kw` of the subgroup `H = U(X₀)`. Let `𝖴` be the unipotent group
`New.Shape.Form.besselU` and let `R = 𝖴 H` be the Bessel group, realised as the subgroup
`New.Shape.besselGraph` of `G₁ × H`. There is a point `x` of bounded size at which the period of a
discrete series coefficient over `R` is large. For a parameter of large gap, the average of the
coefficient over `R` converges absolutely (`integrable_besselIntegrand`). It is a Bessel function
(`isBesselFunction_besselAverage`) that the kernel of the discrete series reproduces
(`convolve_besselAverage`).

## Main definitions and results

* `New.DiscreteSeries.UnitarySignFrame`: a unitary frame taking `J₁` to the diagonal matrix of signs
  `ε`.
* `New.Filling.IsDiscreteSeriesBessel`: the Bessel system has type `(l, kw)`.
* `New.DiscreteSeries.IsSteep.exists_stationary_point`: a point `x` of bounded length at which the
  period over `R` is large, built directly from a Vandermonde/Lagrange frame via Witt's theorem so
  that `besselPairHom x` satisfies `IsLaplaceDatum`.

Notions from other files:
* `New.Shape.G₁`: the unitary group of the complex hermitian form made of ϱ hyperbolic planes, the
  standard positive form on X₀ = ℂ^κ, and one vector z with h(z, z) = −1. Its Gram matrix is
  `splitGram ϱ (middleGram κ 1)`, indexed by `New.Shape.BesselIndex`. Here n = ϱ + 1, k = |κ| and
  r is the dimension of the whole space.
* `New.Shape.besselGraph`: the Bessel group `R = 𝖴 H`, stored as the pairs of an element of G₁ and
  its image in H, with the measure `du dh`.
* `New.simpleRootSum`: the sum of the entries just above the diagonal on the frame e₁, …, e_ϱ, z.
* `New.besselLength`: for y in G₁, the infimum of ‖s y‖ + 1 over s in R; it is the length of y.
* `New.HCParam.HasLargeGap l A`: for `l = 2λ` with N coordinates, the entries are distinct, of the
  parity of N − 1, and entries of `λ` at coordinates of opposite sign are 500 N³ + A apart or more.

## Relation to the literature

See `New.Appendix.DiscreteSeries.Periods` for related work. See
`Lib.DiscreteSeries.Bessel.UnipotentHaarMeasure` for sources.
-/

@[expose] public section

noncomputable section

section BesselType

open Matrix MeasureTheory

/-- A fixed unitary matrix p with pᴴJ₁p the diagonal matrix of the signs ε, where
J₁ = `New.Shape.J₁`. -/
class New.DiscreteSeries.UnitarySignFrame (𝔰 : Shape)
    (ε : outParam (𝔰.BesselIndex → ℤˣ)) extends SignFrame 𝔰.J₁ ε where
  /-- The matrix `p` is unitary. -/
  mem_unitary : matrix.val ∈ unitary (Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)

/-- The Bessel system `B` has type `(l, kw)`: its full function is the Bessel function of the
discrete series of parameter `l`, with values in the representation of `H` of weight `kw`. -/
structure New.Filling.IsDiscreteSeriesBessel {𝔰 : Shape} {ε : 𝔰.BesselIndex → ℤˣ} {b : ℝ} {f : ℕ}
    [DiscreteSeries.UnitarySignFrame 𝔰 ε] (B : BesselSystem 𝔰 b f) (l : HCParam ε)
    (kw : ℕ → ℕ) where
  /-- The degree is given by Weyl's dimension polynomial at `l`. -/
  deg_eq : B.deg = weylDimensionPoly l
  /-- After an invertible change of coordinates `A`, the representation on the values is given by
  the transposed Schur matrix of weight `kw` at `gᵀ`. Here `Unit` is a set of places with one
  point. -/
  exists_conj_rep_eq_schur :
    letI V := WeylIndex 𝔰.κ fun _ : Unit ↦ kw
    ∃ (A : Matrix V B.Index ℂ) (A' : Matrix B.Index V ℂ),
      A * A' = 1 ∧
      A' * A = 1 ∧
      ∀ g : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ),
        A * (B.rep g).val = (schur (fun _ ↦ kw) fun _ ↦ (g : Matrix 𝔰.κ 𝔰.κ ℂ)ᵀ)ᵀ * A
  /-- The full function is fixed by right convolution with the kernel `l.dsKernel`, carried over
  from `USign ε` by the fixed frame. -/
  integral_dsKernel_mul (y : 𝔰.G₁) (i : B.Index) :
    ∫ x : USign ε, l.dsKernel x * B.besselFn .full (y * DiscreteSeries.frameEquiv.symm x) i =
      B.besselFn .full y i
  /-- The full function is `c ∫_R c_l(x⁻¹ s y) π(s)⁻¹ v ds` for a constant `c`, a point `x` and a
  vector `v`, and the integral converges absolutely. Here `c_l` is the coefficient of `l` and `π`
  is the representation of `R` that is given by `B.rep` on `H` and a character on `𝖴`. -/
  exists_eq_besselAverage : ∃ (c : ℝ) (x : 𝔰.G₁) (v : EuclideanSpace ℂ B.Index), ∀ y : 𝔰.G₁,
    Integrable (DiscreteSeries.besselIntegrand l B.rep x v y) 𝔰.besselGraphMeasure ∧
      B.besselFn .full y = c • DiscreteSeries.besselAverage l B.rep x v y

end BesselType

/-!
## The stationary point

Using Lagrange interpolation weights at `0` together with the shifted negative lowest-`K`-type
weights `t i = l.lowestKType (e (.inr i)) - a`, we construct a Vandermonde/Lagrange family of
columns in `ℂ^BesselIndex` whose signed Gram matrix matches that of `X₀` and the Bessel frame
`e₁, …, e_ϱ, z` (together with its dual continuation). Witt's theorem carries these columns to the
standard basis by an element `x ∈ G₁` of controlled `besselLength`, and `besselPairHom x` then
satisfies `IsLaplaceDatum` directly, feeding into `IsLaplaceDatum.laplace_method`.
-/

namespace New

open Matrix Complex Norms.L2Operator ComplexConjugate Finset Fin RealPlace Filling
  IsHermitianInvolution MeasureTheory Subgroup

namespace DiscreteSeries

variable {𝔰 : Shape} {ε : 𝔰.BesselIndex → ℤˣ}

private lemma continuousMul_G₁ : ContinuousMul 𝔰.G₁ := inferInstance

private lemma continuousInv_G₁ : ContinuousInv 𝔰.G₁ := inferInstance

private lemma measurableMul_besselGraph : MeasurableMul 𝔰.besselGraph := inferInstance

private lemma borelSpace_besselGraph : BorelSpace 𝔰.besselGraph := inferInstance

/-- The measure on `R` unfolds 𝖴∖G₁ to G₁: for measurable `f ≥ 0`, the integral of `f (x s y)` over
`s` in `R` and then over `y` in G₁ for `besselQuotMeasure`, which computes integrals over 𝖴∖G₁,
is the integral of `f` over G₁. -/
lemma lintegral_unfold_besselGraphMeasure {x : 𝔰.G₁} (f : 𝔰.G₁ → ENNReal) (hf : Measurable f) :
    ∫⁻ g : 𝔰.G₁, f g = ∫⁻ y : 𝔰.G₁, ∫⁻ s : 𝔰.besselGraph,
      f (x * (s.val.fst * y)) ∂𝔰.besselGraphMeasure ∂besselQuotMeasure := by
  -- Write `s = k * u` with `k` in `H` and `u` in `𝖴`. The integrals over `u` and `y` unfold to one
  -- over the whole group, where left invariance removes `x * k`; and `H` has total mass `1`.
  have : ContinuousMul 𝔰.G₁ := continuousMul_G₁
  have : MeasurableSMul₂ (𝔰.middleGram (1 : ℂ)).besselU 𝔰.G₁ :=
    ⟨((continuous_subtypeVal.comp continuous_fst).fun_mul continuous_snd).measurable⟩
  have : SMulInvariantMeasure (𝔰.middleGram (1 : ℂ)).besselU 𝔰.G₁ volume :=
    ⟨fun c s _ ↦ measure_preimage_mul volume c.val s⟩
  have hf_kg : Measurable fun p : 𝔰.G₁ × U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) ↦
      f (x * (embedH p.2 * p.1)) :=
    hf.comp (continuous_const.fun_mul
      ((continuous_embedH.comp continuous_snd).fun_mul continuous_fst)).measurable
  have h_orbit :
      ∫⁻ y : 𝔰.G₁, ∫⁻ u : (𝔰.middleGram (1 : ℂ)).besselU, ∫⁻ k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ),
          f (x * (embedH k * (u.val * y))) ∂volume ∂𝔰.besselHaar ∂besselQuotMeasure =
        ∫⁻ g : 𝔰.G₁, ∫⁻ k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), f (x * (embedH k * g)) :=
    lintegral_orbitMeasure_lintegral
      (f := fun g : 𝔰.G₁ ↦ ∫⁻ k, f (x * (embedH k * g))) hf_kg.lintegral_prod_right'
  have h_inner (y : 𝔰.G₁) : ∫⁻ s : 𝔰.besselGraph, f (x * (s.val.fst * y)) ∂𝔰.besselGraphMeasure =
      ∫⁻ u : (𝔰.middleGram (1 : ℂ)).besselU, ∫⁻ k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ),
        f (x * (embedH k * (u.val * y))) ∂volume ∂𝔰.besselHaar := by
    have hf_s : Measurable fun s : 𝔰.besselGraph ↦ f (x * (s.val.fst * y)) :=
      hf.comp (continuous_const.fun_mul
        ((continuous_fst.comp continuous_subtypeVal).fun_mul continuous_const)).measurable
    rw [Shape.besselGraphMeasure, lintegral_map hf_s 𝔰.besselGraphChart.measurable]
    simp only [Shape.besselGraphChart_apply_coe]
    rw [lintegral_prod
      (fun p : (𝔰.middleGram (1 : ℂ)).besselU × U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) ↦
        f (x * (embedH p.2 * p.1.val * y)))
      (hf_s.comp 𝔰.besselGraphChart.measurable).aemeasurable]
    simp only [mul_assoc]
  simp_rw [h_inner]
  rw [h_orbit, lintegral_lintegral_swap hf_kg.aemeasurable]
  have h_const (k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) :
      ∫⁻ g : 𝔰.G₁, f (x * (embedH k * g)) = ∫⁻ g : 𝔰.G₁, f g := by
    simp only [← mul_assoc]
    exact lintegral_mul_left_eq_self f (x * embedH k)
  simp_rw [h_const]
  rw [lintegral_const, measure_univ, mul_one]

/-- For `s = (g, h)` in `besselGraph` (so `(embedH h)⁻¹ g ∈ besselU`) and any matrix `M` that is
block upper triangular for `BesselIndex.level`, `tr (M (g - embedH h)) = 0`. Indeed
`g - embedH h = embedH h * (u - 1)` with `u ∈ besselU`; `embedH h` preserves levels while `u - 1`
strictly increases them. -/
lemma besselGraph_trace_mul_sub_eq_zero (s : 𝔰.besselGraph)
    {M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ} (hM : M.BlockTriangular BesselIndex.level) :
    (M * ((s.val.fst : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) -
      (embedH s.val.snd : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ))).trace = 0 := by
  let u : (𝔰.middleGram (1 : ℂ)).besselU := ⟨(embedH s.val.snd)⁻¹ * s.val.fst, s.property⟩
  have hu_mul : (embedH s.val.snd : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) *
      ((u.val : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1) =
      (s.val.fst : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) -
        (embedH s.val.snd : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) := by
    have h_eq : embedH s.val.snd * u.val = s.val.fst := mul_inv_cancel_left _ _
    rw [mul_sub_one, ← Units.val_mul, ← Subgroup.coe_mul, h_eq]
  have h_embedH_tri :
      (embedH s.val.snd : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ).BlockTriangular
        BesselIndex.level := by
    intro i j hij
    rcases i with a | ((i₀ | ⟨⟩) | a) <;> rcases j with b | ((j₀ | ⟨⟩) | b) <;>
      simp [BesselIndex.level, val_toBesselH_apply_coe, Matrix.one_apply] at hij ⊢ <;>
      · rintro rfl; exact lt_irrefl _ hij
  have hM' : (M * (embedH s.val.snd : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)).BlockTriangular
      BesselIndex.level := hM.mul h_embedH_tri
  rw [← hu_mul, ← Matrix.mul_assoc, trace]
  refine sum_eq_zero fun i _ ↦ ?_
  rw [diag_apply, Matrix.mul_apply]
  refine sum_eq_zero fun j _ ↦ ?_
  rcases lt_or_ge (BesselIndex.level j) (BesselIndex.level i) with hij | hij
  · rw [hM' hij, zero_mul]
  · have hu_entry : (u.val : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) j i =
        (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) j i :=
      mem_besselU.1 u.property j i hij
    rw [Matrix.sub_apply, hu_entry, sub_self, mul_zero]

variable [p : UnitarySignFrame 𝔰 ε]

/-- The map `s ↦ (x⁻¹ s x, h)`, where `h` is the image of `s` in `H` and `x⁻¹ s x` is written in the
frame of signs `ε`. -/
def besselPairHom (x : 𝔰.G₁) : 𝔰.besselGraph →* USign ε × USign (1 : 𝔰.κ → ℤˣ) :=
  .domRestrict (.prodMap (.comp (frameEquiv (ε := ε)) (MulAut.conj x⁻¹).toMonoidHom)
    (inclusion (by simp [USign]))) 𝔰.besselGraph

/-- The first component `s ↦ x⁻¹ s x` of `besselPairHom x` is proper: `R` is closed in `G₁ × H` and
`H` is compact. -/
lemma isProperMap_besselPairHom_fst (x : 𝔰.G₁) :
    IsProperMap fun s : 𝔰.besselGraph ↦ (besselPairHom (ε := ε) x s).fst := by
  exact ((Homeomorph.smul (x⁻¹ : ConjAct 𝔰.G₁)).trans frameEquiv.toHomeomorph).isProperMap.comp
    (isProperMap_fst_of_compactSpace.restrict inferInstance)

/-- The first entry of `subOnePair (besselPairHom x) s`, the first component minus one, is the
conjugate of `s - 1` by `x p`, where `p` is the frame of signs `ε`. -/
lemma subOnePair_besselPairHom_fst (s : 𝔰.besselGraph) (x : 𝔰.G₁) :
    (subOnePair (besselPairHom x) s).fst =
      (x.val * p.matrix)⁻¹.val * ((s.val.fst : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1) *
        (x.val * p.matrix).val := by
  change p.matrix⁻¹.val * (x⁻¹.val.val * s.val.fst.val.val * x.val.val) * p.matrix.val - 1 = _
  rw [_root_.mul_inv_rev, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.val_mul,
    Units.val_mul]
  have h1 : p.matrix⁻¹.val * x.val⁻¹.val * (x.val.val * p.matrix.val) = 1 := by
    rw [Matrix.mul_assoc p.matrix⁻¹.val, ← Matrix.mul_assoc x.val⁻¹.val,
      show x.val⁻¹.val * x.val.val = 1 from x.val.inv_mul, Matrix.one_mul, Units.inv_mul]
  rw [h1]
  refine congrArg (· - 1) ?_
  simp only [Matrix.mul_assoc]
  rfl

/-- The second component of `besselPairHom x s` has the matrix of the image of `s` in `H`. -/
lemma besselPairHom_snd_val (s : 𝔰.besselGraph) (x : 𝔰.G₁) :
    ((besselPairHom (ε := ε) x s).snd : Matrix 𝔰.κ 𝔰.κ ℂ) = (s.val.snd : Matrix 𝔰.κ 𝔰.κ ℂ) := rfl

/-- The second entry of `subOnePair (besselPairHom x) s` is the image of `s` in `H`, minus one. -/
lemma subOnePair_besselPairHom_snd (s : 𝔰.besselGraph) (x : 𝔰.G₁) :
    (subOnePair (besselPairHom (ε := ε) x) s).snd = (s.val.snd : Matrix 𝔰.κ 𝔰.κ ℂ) - 1 := rfl

/-- The unitary frame `p` takes a vector with entries of modulus at most `M` to one of length at
most `√r M`, where `r` is the dimension. -/
lemma norm_frame_mulVec_le {M : ℝ} (hM : 0 ≤ M) {w : 𝔰.BesselIndex → ℂ}
    (hw : ∀ i : 𝔰.BesselIndex, ‖w i‖ ≤ M) :
    ‖WithLp.toLp 2 (p.matrix.val *ᵥ w)‖ ≤ √𝔰.r * M := by
  have h_sum : ∑ i : 𝔰.BesselIndex, ‖w i‖ ^ 2 ≤ 𝔰.r * M ^ 2 := by
    have h := sum_le_card_nsmul univ (fun i : 𝔰.BesselIndex ↦ ‖w i‖ ^ 2) (M ^ 2) fun i _ ↦
      pow_le_pow_left₀ (norm_nonneg _) (hw i) 2
    rwa [card_univ, nsmul_eq_mul] at h
  refine (l2_opNorm_mulVec p.matrix.val (WithLp.toLp 2 w)).trans ?_
  rw [CStarRing.norm_of_mem_unitary p.mem_unitary, one_mul, EuclideanSpace.norm_eq]
  calc √(∑ i : 𝔰.BesselIndex, ‖w i‖ ^ 2)
      ≤ √(𝔰.r * M ^ 2) := Real.sqrt_le_sqrt h_sum
    _ = √𝔰.r * M := by rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hM]

/-- **Direct Laplace datum for the Bessel subgroup.** Let `l` on `U(ε)` be steep with bound `B ≥ 1`
for `e : X ⊕ Fin (2 ϱ + 2) ≃ BesselIndex`, and let `u` on `H = U(κ)` have lowest-`K`-type weight `a`
at `τ (.inr ())` and `0` on `τ (.inl X)`. If `3 B + a ≤ b ^ 2` and `8 n r ≤ b`, there is `x ∈ G₁`
with `besselLength x ≤ b ^ (5 n)` such that `besselPairHom x` satisfies `IsLaplaceDatum` directly
with phase `s ↦ simpleRootSum s.1 - conj (simpleRootSum s.1)`. -/
lemma IsSteep.exists_isLaplaceDatum_besselPairHom {X : Type} [Fintype X] [DecidableEq X]
    {l : HCParam ε} {u : HCParam (1 : 𝔰.κ → ℤˣ)}
    {e : X ⊕ Fin (2 * 𝔰.ϱ + 2) ≃ 𝔰.BesselIndex} {B b : ℝ} {a : ℕ}
    (h_steep : IsSteep l B e) (τ : X ⊕ Unit ≃ 𝔰.κ)
    (ha : ∀ i : 𝔰.κ, u.lowestKType i = if i = τ (Sum.inr ()) then (a : ℤ) else 0)
    (hB : 1 ≤ B) (hb : 3 * B + a ≤ b ^ 2) (hb_rank : 8 * 𝔰.n * 𝔰.r ≤ b) :
    ∃ x : 𝔰.G₁,
      besselLength x ≤ b ^ (5 * 𝔰.n) ∧
      IsLaplaceDatum l u (besselPairHom x) (τ ∘ Sum.inl) B e
        (fun s : 𝔰.besselGraph ↦ simpleRootSum s.val.fst - conj (simpleRootSum s.val.fst)) := by
  have hr_one : (1 : ℝ) ≤ 𝔰.r := Nat.one_le_cast.2 Fintype.card_pos
  have hn_one : (1 : ℝ) ≤ 𝔰.n := Nat.one_le_cast.2 (Nat.le_add_left 1 𝔰.ϱ)
  have hb_one : 1 ≤ b := by nlinarith
  -- Shifts `t i = μ_l (e (.inr i)) - a` are strictly decreasing and strictly negative, so
  -- prepending `0` yields `2 ϱ + 3` strictly decreasing integer nodes.
  let t (i : Fin (2 * 𝔰.ϱ + 2)) : ℤ := l.lowestKType (e (.inr i)) - a
  let nodes : Fin (2 * 𝔰.ϱ + 3) → ℤ := Fin.cons 0 t
  have h_nodes_anti : StrictAnti nodes := by
    intro i j hij
    refine Fin.cases (fun j hij ↦ ?_) (fun i' j hij ↦ ?_) i j hij
    · refine Fin.cases (fun hij ↦ absurd hij (lt_irrefl 0)) (fun j' _ ↦ ?_) j hij
      simp only [nodes, cons_zero, cons_succ, t]
      have h_lt : ((l.lowestKType (e (.inr j')) - (a : ℤ) : ℤ) : ℝ) < (0 : ℤ) := by
        push_cast
        linarith [(h_steep.weight_mem j').2, (Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
      exact Int.cast_lt.1 h_lt
    · refine Fin.cases (fun hij ↦ absurd hij (Fin.not_lt_zero _)) (fun j' hij ↦ ?_) j hij
      simp only [nodes, cons_succ, t]
      have h_lt := h_steep.weight_strictAnti (succ_lt_succ_iff.1 hij)
      dsimp only at h_lt
      omega
  obtain ⟨c, hc, h_lagrange⟩ := exists_lagrange_weights h_nodes_anti
  -- Build the Vandermonde/Lagrange columns `w n` (`n : ℕ`), scaled by `c 0` at `n = 0`.
  let w (n : ℕ) (i : Fin (2 * 𝔰.ϱ + 2)) : ℝ :=
    (if n = 0 then c 0 else 1) * (t i : ℝ) ^ n / c i.succ
  have h_gram_w {n₁ n₂ : ℕ} (hn : n₁.pred + n₂.pred ≤ 2 * 𝔰.ϱ) :
      ∑ i : Fin (2 * 𝔰.ϱ + 2), (-1 : ℝ) ^ i.val * (w n₁ i * w n₂ i) =
        if n₁ + n₂ = 0 then 1 else if n₁ + n₂ = 2 * 𝔰.ϱ + 2 then -1 else 0 := by
    have hn_sum : n₁ + n₂ ≤ 2 * 𝔰.ϱ + 2 := by
      simp only [Nat.pred_eq_sub_one] at hn
      omega
    let P : Polynomial ℝ := Polynomial.X ^ (n₁ + n₂)
    have hP_deg : P.degree < (2 * 𝔰.ϱ + 3 : ℕ) :=
      (Polynomial.degree_X_pow (n₁ + n₂)).trans_lt (by norm_cast; omega)
    have h_res := h_lagrange P hP_deg
    rw [show 2 * 𝔰.ϱ + 3 - 1 = 2 * 𝔰.ϱ + 2 by omega, Polynomial.coeff_X_pow,
      Fin.sum_univ_succ] at h_res
    simp only [P, nodes, cons_zero, cons_succ, Int.cast_zero, Polynomial.eval_pow,
      Polynomial.eval_X, val_zero, pow_zero, one_mul] at h_res
    have h_tail : ∑ i : Fin (2 * 𝔰.ϱ + 2),
        (-1 : ℝ) ^ i.succ.val * ((t i : ℝ) ^ (n₁ + n₂) / c i.succ ^ 2) =
          -∑ i : Fin (2 * 𝔰.ϱ + 2),
            (-1 : ℝ) ^ i.val * ((t i : ℝ) ^ (n₁ + n₂) / c i.succ ^ 2) := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [val_succ, pow_succ]
      ring
    rw [h_tail] at h_res
    set s₁ : ℝ := if n₁ = 0 then c 0 else 1
    set s₂ : ℝ := if n₂ = 0 then c 0 else 1
    have h_scaled := congrArg (s₁ * s₂ * ·) h_res
    have h_sum_eq : s₁ * s₂ * ∑ i : Fin (2 * 𝔰.ϱ + 2),
        (-1 : ℝ) ^ i.val * ((t i : ℝ) ^ (n₁ + n₂) / c i.succ ^ 2) =
          ∑ i : Fin (2 * 𝔰.ϱ + 2), (-1 : ℝ) ^ i.val * (w n₁ i * w n₂ i) := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ ↦ ?_
      simp only [w, pow_add]
      ring
    by_cases h0 : n₁ + n₂ = 0
    · obtain ⟨rfl, rfl⟩ : n₁ = 0 ∧ n₂ = 0 := Nat.add_eq_zero_iff.1 h0
      have hc0_ne : c 0 ≠ 0 := by linarith [(hc 0).1]
      have h_ne_top : (2 * 𝔰.ϱ + 2 : ℕ) ≠ 0 := by omega
      simp only [s₁, s₂, ite_true, add_zero, h_ne_top, ite_false, pow_zero] at h_scaled h_sum_eq
      rw [ite_eq_left rfl]
      have h_c0 : c 0 * c 0 * (1 / c 0 ^ 2) = 1 := by field_simp [hc0_ne]
      linarith [h_scaled, h_sum_eq, h_c0]
    · rw [ite_eq_right h0]
      rw [zero_pow h0, zero_div, zero_add] at h_scaled
      rcases eq_or_ne (n₁ + n₂) (2 * 𝔰.ϱ + 2) with h_top | h_not_top
      · have hn₁ : n₁ ≠ 0 := by simp only [Nat.pred_eq_sub_one] at hn; omega
        have hn₂ : n₂ ≠ 0 := by simp only [Nat.pred_eq_sub_one] at hn; omega
        simp only [s₁, s₂, hn₁, hn₂, ite_false, h_top, ite_true, one_mul] at h_scaled h_sum_eq ⊢
        linarith [h_scaled, h_sum_eq]
      · simp only [Ne.symm h_not_top, h_not_top, ite_false, mul_zero] at h_scaled ⊢
        linarith [h_scaled, h_sum_eq]
  -- Place `1` on `X` and `w` on `Fin (2 ϱ + 2)`, then map to `G₁` via the unitary sign frame `p`.
  let C₀ : Matrix (X ⊕ Fin (2 * 𝔰.ϱ + 2)) (X ⊕ ℕ) ℂ :=
    fromBlocks 1 0 0 (of fun (i : Fin (2 * 𝔰.ϱ + 2)) (n : ℕ) ↦ (w n i : ℂ))
  let C : Matrix 𝔰.BesselIndex (X ⊕ ℕ) ℂ := C₀.submatrix e.symm id
  let V : Matrix 𝔰.BesselIndex (X ⊕ ℕ) ℂ := p.matrix.val * C
  have hV_gram {col₁ col₂ : X ⊕ ℕ}
      (h_deg : col₁.elim (fun _ ↦ 0) Nat.pred + col₂.elim (fun _ ↦ 0) Nat.pred ≤ 2 * 𝔰.ϱ) :
      (Vᴴ * 𝔰.J₁ * V) col₁ col₂ =
        fromBlocks 1 0 0
          (of fun n₁ n₂ : ℕ ↦
            if n₁ + n₂ = 0 then (1 : ℂ) else if n₁ + n₂ = 2 * 𝔰.ϱ + 2 then -1 else 0)
          col₁ col₂ := by
    have h_eq : Vᴴ * 𝔰.J₁ * V = Cᴴ * signMatrix ε * C := by
      simp only [V, conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc p.matrix.valᴴ, ← Matrix.mul_assoc (p.matrix.valᴴ * 𝔰.J₁), p.gram_eq]
    rw [h_eq, signMatrix, Matrix.mul_apply, ← e.sum_comp, Fintype.sum_sum_type]
    rcases col₁ with x₁ | n₁ <;> rcases col₂ with x₂ | n₂
    · simp [C, C₀, mul_diagonal, h_steep.sign_inl, Matrix.one_apply, eq_comm]
    · simp [C, C₀, mul_diagonal]
    · simp [C, C₀, mul_diagonal]
    · have h_real := congrArg Complex.ofReal (h_gram_w (by simpa using h_deg))
      simp only [ofReal_sum, ofReal_mul, ofReal_pow, ofReal_neg, ofReal_one,
        apply_ite Complex.ofReal, ofReal_zero] at h_real
      simp only [C, C₀, mul_diagonal, conjTranspose_apply, submatrix_apply, id_eq,
        Equiv.symm_apply_apply, fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply,
        of_apply, star_zero, Complex.star_def, conj_ofReal, h_steep.sign_inr, Units.val_one,
        Units.val_pow_eq_pow_val, Units.val_neg, Int.cast_pow, Int.cast_neg, Int.cast_one,
        zero_mul, mul_zero, sum_const_zero, zero_add]
      rw [← h_real]
      exact sum_congr rfl fun i _ ↦ by ring
  -- Select the `X₀` columns (`.inl x₀` and `.inr 0`) and the `ϱ + 1` frame columns
  -- (`.inr (a + 1)`), and match them to the standard basis columns `Y` by Witt's theorem.
  let f : (X ⊕ Unit) ⊕ Fin (𝔰.ϱ + 1) → X ⊕ ℕ :=
    Sum.elim (Sum.map id fun _ ↦ 0) fun a ↦ Sum.inr (a.val + 1)
  let f' : (X ⊕ Unit) ⊕ Fin (𝔰.ϱ + 1) → X ⊕ ℕ :=
    Sum.elim (Sum.map id fun _ ↦ 0) fun a ↦ Sum.inr (2 * 𝔰.ϱ + 1 - a.val)
  let Y : Matrix 𝔰.BesselIndex ((X ⊕ Unit) ⊕ Fin (𝔰.ϱ + 1)) ℂ :=
    inclMatrix ℂ (Sum.elim (𝔰.indexX₀ ∘ τ) 𝔰.besselFrame)
  have h_frame_ne_X₀ (u₀ : X ⊕ Unit) (a₀ : Fin (𝔰.ϱ + 1)) :
      𝔰.indexX₀ (τ u₀) ≠ 𝔰.besselFrame a₀ := by
    simp only [Shape.besselFrame, snoc, Shape.indexX₀, Shape.z]; split_ifs <;> simp
  have h_frame_inj : Function.Injective 𝔰.besselFrame := fun a₁ a₂ h ↦ by
    simp only [Shape.besselFrame, snoc, Shape.z] at h
    split_ifs at h with h₁ h₂ <;> simp at h
    · exact Fin.ext (by simpa [Fin.ext_iff] using h)
    · exact Fin.ext (by omega)
  have hJ_X₀_frame (u₀ : X ⊕ Unit) (a₀ : Fin (𝔰.ϱ + 1)) :
      𝔰.J₁ (𝔰.indexX₀ (τ u₀)) (𝔰.besselFrame a₀) = 0 := by
    simp only [Shape.besselFrame, snoc, Shape.indexX₀, Shape.z]
    split_ifs <;> simp [splitGram, middleGram]
  have hJ_frame_X₀ (a₀ : Fin (𝔰.ϱ + 1)) (u₀ : X ⊕ Unit) :
      𝔰.J₁ (𝔰.besselFrame a₀) (𝔰.indexX₀ (τ u₀)) = 0 := by
    simp only [Shape.besselFrame, snoc, Shape.indexX₀, Shape.z]
    split_ifs <;> simp [splitGram, middleGram]
  have hJ_frame_frame (a₁ a₂ : Fin (𝔰.ϱ + 1)) :
      𝔰.J₁ (𝔰.besselFrame a₁) (𝔰.besselFrame a₂) =
        if a₁ = last 𝔰.ϱ ∧ a₂ = last 𝔰.ϱ then -1 else 0 := by
    have h_eq (a : Fin (𝔰.ϱ + 1)) : a = last 𝔰.ϱ ↔ ¬(a.val < 𝔰.ϱ) := by
      simp only [Fin.ext_iff, val_last]; omega
    simp only [Shape.besselFrame, snoc, Shape.z, h_eq]
    split_ifs <;> simp_all [splitGram, middleGram]
  have hV_inl (u₁ u₂ : X ⊕ Unit) :
      (Vᴴ * 𝔰.J₁ * V) (f (.inl u₁)) (f (.inl u₂)) = if u₁ = u₂ then 1 else 0 := by
    rcases u₁ with x₁ | ⟨⟩ <;> rcases u₂ with x₂ | ⟨⟩ <;>
      rw [hV_gram (by simp [f])] <;> simp [f, Matrix.one_apply]
  have h_indep_V : HasLeftInv (V.submatrix id f) := by
    let lev : (X ⊕ Unit) ⊕ Fin (𝔰.ϱ + 1) → ℕ := Sum.elim (fun _ ↦ 0) fun b ↦ b.val + 1
    let Dsgn : Matrix ((X ⊕ Unit) ⊕ Fin (𝔰.ϱ + 1)) ((X ⊕ Unit) ⊕ Fin (𝔰.ϱ + 1)) ℂ :=
      diagonal (Sum.elim (1 : X ⊕ Unit → ℂ) (-1))
    let Z : Matrix ((X ⊕ Unit) ⊕ Fin (𝔰.ϱ + 1)) ((X ⊕ Unit) ⊕ Fin (𝔰.ϱ + 1)) ℂ :=
      Dsgn * ((V.submatrix id f')ᴴ * 𝔰.J₁ * V.submatrix id f)
    have hZ_tri : ∀ row col : (X ⊕ Unit) ⊕ Fin (𝔰.ϱ + 1),
        lev col ≤ lev row → Z row col = (1 : Matrix _ _ ℂ) row col := by
      intro row col h_le
      have h_prod : ((V.submatrix id f')ᴴ * 𝔰.J₁ * V.submatrix id f) row col =
          (Vᴴ * 𝔰.J₁ * V) (f' row) (f col) := by simp [Matrix.mul_apply]
      dsimp only [Z, Dsgn]
      rw [diagonal_mul, h_prod]
      rcases row with u₁ | a₁ <;> rcases col with u₂ | a₂
      · simpa [f', f, Matrix.one_apply] using hV_inl u₁ u₂
      · exfalso; simp only [lev, Sum.elim_inl, Sum.elim_inr] at h_le; omega
      · rcases u₂ with x₂ | ⟨⟩ <;> rw [hV_gram (by simp [f', f])]
        · simp [f', f]
        · simp [f', f, show 2 * 𝔰.ϱ + 1 - a₁.val ≠ 0 by omega,
            show 2 * 𝔰.ϱ + 1 - a₁.val ≠ 2 * 𝔰.ϱ + 2 by omega]
      · simp only [lev, Sum.elim_inr] at h_le
        rw [hV_gram (by simp [f', f]; omega)]
        have h_ne0 : 2 * 𝔰.ϱ + 1 - a₁.val + (a₂.val + 1) ≠ 0 := by omega
        have h_top_iff : 2 * 𝔰.ϱ + 1 - a₁.val + (a₂.val + 1) = 2 * 𝔰.ϱ + 2 ↔ a₁ = a₂ := by
          rw [Fin.ext_iff]; omega
        simp only [Sum.elim_inr, Pi.neg_apply, Pi.one_apply, f', f, fromBlocks_apply₂₂, of_apply,
          h_ne0, ite_false, h_top_iff]
        rcases eq_or_ne a₁ a₂ with rfl | hab <;> simp [*]
    have hZ_unit : IsUnit Z.det := by rw [det_eq_one_of_unitriangular hZ_tri]; exact isUnit_one
    exact ⟨Z⁻¹ * (Dsgn * ((V.submatrix id f')ᴴ * 𝔰.J₁)),
      (by simp only [Z, Matrix.mul_assoc] : _ = Z⁻¹ * Z).trans (nonsing_inv_mul Z hZ_unit)⟩
  have h_indep_Y : HasLeftInv Y := ⟨Yᴴ, by
    ext (u₁ | a₁) (u₂ | a₂) <;>
      simp [Y, inclMatrix, Matrix.mul_apply, Matrix.one_apply, h_frame_ne_X₀,
        (h_frame_ne_X₀ _ _).symm, h_frame_inj.eq_iff, eq_comm]⟩
  have h_gram_eq : (V.submatrix id f)ᴴ * 𝔰.J₁ * V.submatrix id f = Yᴴ * 𝔰.J₁ * Y := by
    ext row col
    have h_lhs : ((V.submatrix id f)ᴴ * 𝔰.J₁ * V.submatrix id f) row col =
        (Vᴴ * 𝔰.J₁ * V) (f row) (f col) := by simp [Matrix.mul_apply]
    have h_rhs : (Yᴴ * 𝔰.J₁ * Y) row col =
        𝔰.J₁ ((Sum.elim (𝔰.indexX₀ ∘ τ) 𝔰.besselFrame) row)
          ((Sum.elim (𝔰.indexX₀ ∘ τ) 𝔰.besselFrame) col) := by
      rw [Matrix.mul_assoc, mul_inclMatrix, Matrix.mul_apply]
      simp [Y, inclMatrix, Matrix.one_apply]
    rw [h_lhs, h_rhs]
    rcases row with u₁ | a₁ <;> rcases col with u₂ | a₂
    · rw [hV_inl u₁ u₂]; simp [splitGram, middleGram, Matrix.one_apply]
    · rcases u₁ with x₁ | ⟨⟩ <;> rw [hV_gram (by simp [f]; omega)]
      · simp [f, hJ_X₀_frame]
      · simp [f, hJ_X₀_frame, show a₂.val ≠ 2 * 𝔰.ϱ + 1 by omega]
    · rcases u₂ with x₂ | ⟨⟩ <;> rw [hV_gram (by simp [f]; omega)]
      · simp [f, hJ_frame_X₀]
      · simp [f, hJ_frame_X₀, show a₁.val ≠ 2 * 𝔰.ϱ + 1 by omega]
    · rw [hV_gram (by simp [f]; omega)]
      have h_top_iff : a₁.val + 1 + (a₂.val + 1) = 2 * 𝔰.ϱ + 2 ↔
          a₁ = last 𝔰.ϱ ∧ a₂ = last 𝔰.ϱ := by simp only [Fin.ext_iff, val_last]; omega
      simp [f, h_top_iff, hJ_frame_frame]
  obtain ⟨x, hx⟩ : ∃ x : 𝔰.G₁, x.val.val * V.submatrix id f = Y :=
    witt ⟨Complex.I, by simp⟩ isHermitian.eq IsHermitianInvolution.isUnit h_indep_V h_indep_Y
      h_gram_eq
  let q : GL 𝔰.BesselIndex ℂ := x.val * p.matrix
  have hq_Y : q.val * C.submatrix id f = Y := by
    have h_sub : V.submatrix id f = p.matrix.val * C.submatrix id f := by
      ext i j; simp [V, Matrix.mul_apply]
    simpa [q, h_sub, Matrix.mul_assoc] using hx
  have hq_gram : q.valᴴ * 𝔰.J₁ * q.val = signMatrix ε :=
    gram_mul_of_gram_eq (mem_unitaryGroupOf_iff.1 x.property) p.gram_eq
  -- Bound `besselLength x` using the dual continuation `V (.inr (k + 1))` (`k ≤ 2 ϱ`).
  have hx_len : besselLength x ≤ b ^ (5 * 𝔰.n) := by
    let seq (k : ℕ) : EuclideanSpace ℂ 𝔰.BesselIndex :=
      WithLp.toLp 2 (p.matrix.val *ᵥ fun i : 𝔰.BesselIndex ↦ C i (.inr (k + 1)))
    have h_frame_vec (k : Fin (𝔰.ϱ + 1)) : frameVector x k = seq k.val := by
      have hx_inv : x⁻¹.val.val * x.val.val = 1 := x.val.inv_val
      have h_inv : x⁻¹.val.val * Y = V.submatrix id f := by
        rw [← hx, ← Matrix.mul_assoc, hx_inv, Matrix.one_mul]
      ext i
      have h_col := congrFun₂ h_inv i (.inr k)
      have hY_col : (x⁻¹.val.val * Y) i (.inr k) = frameVector x k i := by
        simpa [frameVector, Y] using congrFun₂ (mul_inclMatrix x⁻¹.val.val
          (Sum.elim (𝔰.indexX₀ ∘ τ) 𝔰.besselFrame)) i (.inr k)
      rw [← hY_col, h_col]
      simp only [seq, V, f, submatrix_apply, id_eq, Sum.elim_inr, mulVec, dotProduct,
        Matrix.mul_apply]
    have h_entry_le (k : ℕ) (hk : k ≤ 2 * 𝔰.ϱ) (i : 𝔰.BesselIndex) :
        ‖C i (.inr (k + 1))‖ ≤ (b ^ 2) ^ (2 * 𝔰.ϱ + 1) := by
      obtain ⟨x₀ | i₀, rfl⟩ := e.surjective i
      · simp [C, C₀, show (0 : ℝ) ≤ (b ^ 2) ^ (2 * 𝔰.ϱ + 1) by positivity]
      · have ht_abs : |(t i₀ : ℝ)| ≤ b ^ 2 := by
          simp only [t, Int.cast_sub, Int.cast_natCast]
          exact (abs_le.2 ⟨by linarith [(h_steep.weight_mem i₀).1,
            (Nat.cast_nonneg a : (0 : ℝ) ≤ a)],
            by linarith [(h_steep.weight_mem i₀).2,
              (Nat.cast_nonneg a : (0 : ℝ) ≤ a)]⟩).trans hb
        have hc_ge : 1 ≤ c i₀.succ := (hc i₀.succ).1
        have hw_abs : |w (k + 1) i₀| ≤ (b ^ 2) ^ (2 * 𝔰.ϱ + 1) := by
          simp only [w, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, one_mul, abs_div,
            abs_pow]
          calc |(t i₀ : ℝ)| ^ (k + 1) / |c i₀.succ|
              ≤ |(t i₀ : ℝ)| ^ (k + 1) :=
                div_le_self (by positivity) (by rwa [abs_of_pos (by linarith)])
            _ ≤ (b ^ 2) ^ (k + 1) := pow_le_pow_left₀ (abs_nonneg _) ht_abs _
            _ ≤ (b ^ 2) ^ (2 * 𝔰.ϱ + 1) :=
                pow_le_pow_right₀ (one_le_pow₀ hb_one) (by omega)
        simpa [C, C₀] using hw_abs
    have h_seq_norm (k : ℕ) (hk : k ≤ 2 * 𝔰.ϱ) :
        ‖seq k‖ ≤ √𝔰.r * (b ^ 2) ^ (2 * 𝔰.ϱ + 1) :=
      norm_frame_mulVec_le (by positivity) (h_entry_le k hk)
    have h_seq_dual (k₁ k₂ : ℕ) (hk : k₁ + k₂ ≤ 2 * 𝔰.ϱ) :
        inner ℂ (seq k₁) (Matrix.toEuclideanLin 𝔰.J₁ (seq k₂)) =
          if k₁ + k₂ = 2 * 𝔰.ϱ then -1 else 0 := by
      have h_entry := hV_gram (col₁ := .inr (k₁ + 1)) (col₂ := .inr (k₂ + 1))
        (by simpa using hk)
      have h_ne0 : k₁ + 1 + (k₂ + 1) ≠ 0 := by omega
      have h_top : k₁ + 1 + (k₂ + 1) = 2 * 𝔰.ϱ + 2 ↔ k₁ + k₂ = 2 * 𝔰.ϱ := by omega
      simp only [fromBlocks_apply₂₂, of_apply, h_ne0, ite_false, h_top] at h_entry
      have h_col_eq (k : ℕ) : (seq k : 𝔰.BesselIndex → ℂ) = V.col (.inr (k + 1)) := by
        ext i
        simp only [seq, V, col_apply, mulVec, dotProduct, Matrix.mul_apply]
      have h_inner_eq : inner ℂ (seq k₁) (Matrix.toEuclideanLin 𝔰.J₁ (seq k₂)) =
          (Vᴴ * 𝔰.J₁ * V) (.inr (k₁ + 1)) (.inr (k₂ + 1)) := by
        change (𝔰.J₁ *ᵥ seq k₂) ⬝ᵥ star (seq k₁ : 𝔰.BesselIndex → ℂ) = _
        rw [dotProduct_comm, h_col_eq, h_col_eq]
        exact (congrFun₂ (Matrix.mul_assoc Vᴴ 𝔰.J₁ V) (.inr (k₁ + 1)) (.inr (k₂ + 1))).symm
      exact h_inner_eq.trans h_entry
    have hM_one : 1 ≤ √(𝔰.r : ℝ) * (b ^ 2) ^ (2 * 𝔰.ϱ + 1) :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.2 hr_one)
        (one_le_pow₀ (one_le_pow₀ hb_one))
    have h_bound := besselLength_le_of_dual (y := x) hM_one seq h_frame_vec h_seq_norm h_seq_dual
    have h_sqrt_le : √(𝔰.r : ℝ) ≤ 𝔰.r :=
      Real.sqrt_le_iff.2 ⟨by positivity, le_self_pow₀ hr_one two_ne_zero⟩
    calc besselLength x
        ≤ 8 * (𝔰.ϱ + 1 : ℝ) * (√𝔰.r * (b ^ 2) ^ (2 * 𝔰.ϱ + 1)) := h_bound
      _ ≤ 8 * 𝔰.n * 𝔰.r * (b ^ 2) ^ (2 * 𝔰.ϱ + 1) := by
          have hn_eq : (𝔰.ϱ + 1 : ℝ) = 𝔰.n := by norm_cast
          rw [hn_eq, mul_assoc (8 * (𝔰.n : ℝ))]
          gcongr
      _ ≤ b * b ^ (4 * 𝔰.ϱ + 2) := by
          rw [← pow_mul, show 2 * (2 * 𝔰.ϱ + 1) = 4 * 𝔰.ϱ + 2 by ring]
          gcongr
      _ ≤ b ^ (5 * 𝔰.n) := by
          rw [← pow_succ']
          exact pow_le_pow_right₀ hb_one (by have : 𝔰.n = 𝔰.ϱ + 1 := rfl; omega)
  -- Verify `IsLaplaceDatum` for `besselPairHom x` via `D = q * diag(μ_l) * q⁻¹`.
  let D : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ := q.val * intDiagonal l.lowestKType * q⁻¹.val
  have hD_Y : D * Y = q.val * (intDiagonal l.lowestKType * C.submatrix id f) := by
    simp only [D, ← hq_Y, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc q⁻¹.val q.val, Units.inv_mul, Matrix.one_mul]
  have hY_col (col : (X ⊕ Unit) ⊕ Fin (𝔰.ϱ + 1)) (row : 𝔰.BesselIndex) :
      (D * Y) row col = D row ((Sum.elim (𝔰.indexX₀ ∘ τ) 𝔰.besselFrame) col) := by
    simpa [Y] using congrFun₂ (mul_inclMatrix D (Sum.elim (𝔰.indexX₀ ∘ τ) 𝔰.besselFrame)) row col
  have hC_shift_inl_inl (x₀ : X) (i : 𝔰.BesselIndex) :
      (intDiagonal l.lowestKType * C.submatrix id f) i (.inl (.inl x₀)) = 0 := by
    obtain ⟨x₁ | i₀, rfl⟩ := e.surjective i <;>
      simp [C, C₀, f, diagonal_mul, h_steep.weight_eq_zero]
  have hC_shift_inl_inr (i : 𝔰.BesselIndex) :
      (intDiagonal l.lowestKType * C.submatrix id f) i (.inl (.inr ())) =
        (a : ℂ) * C.submatrix id f i (.inl (.inr ())) +
          (c 0 : ℂ) * C.submatrix id f i (.inr 0) := by
    obtain ⟨x₁ | i₀, rfl⟩ := e.surjective i
    · simp [C, C₀, f, diagonal_mul, h_steep.weight_eq_zero]
    · have ht_eq : (l.lowestKType (e (.inr i₀)) : ℂ) = (a : ℂ) + (t i₀ : ℂ) := by simp [t]
      simp only [submatrix_apply, id_eq, diagonal_mul, intDiagonal, ht_eq, C, C₀,
        Equiv.symm_apply_apply, f, Sum.elim_inl, Sum.map_inr, fromBlocks_apply₂₂, of_apply,
        Sum.elim_inr, val_zero, zero_add, w, ite_true, pow_zero, mul_one, one_ne_zero, ite_false,
        one_mul, pow_one]
      push_cast
      ring
  have hC_shift_inr (b₀ : Fin 𝔰.ϱ) (i : 𝔰.BesselIndex) :
      (intDiagonal l.lowestKType * C.submatrix id f) i (.inr b₀.castSucc) =
        (a : ℂ) * C.submatrix id f i (.inr b₀.castSucc) +
          C.submatrix id f i (.inr b₀.succ) := by
    obtain ⟨x₁ | i₀, rfl⟩ := e.surjective i
    · simp [C, C₀, f, diagonal_mul, h_steep.weight_eq_zero]
    · have ht_eq : (l.lowestKType (e (.inr i₀)) : ℂ) = (a : ℂ) + (t i₀ : ℂ) := by simp [t]
      have h_ne1 : b₀.val + 1 ≠ 0 := by omega
      simp only [submatrix_apply, id_eq, diagonal_mul, intDiagonal, ht_eq, C, C₀,
        Equiv.symm_apply_apply, f, Sum.elim_inr, val_castSucc, fromBlocks_apply₂₂, of_apply, w,
        h_ne1, ite_false, one_mul, val_succ]
      push_cast
      ring
  have hD_on_X (x₀ : X) (row : 𝔰.BesselIndex) : D row (𝔰.indexX₀ (τ (.inl x₀))) = 0 := by
    have hcol : (D * Y) row (.inl (.inl x₀)) = D row (𝔰.indexX₀ (τ (.inl x₀))) :=
      hY_col (.inl (.inl x₀)) row
    rw [← hcol, hD_Y, Matrix.mul_apply]
    simp [hC_shift_inl_inl]
  have hD_on_unit (row : 𝔰.BesselIndex) :
      D row (𝔰.indexX₀ (τ (.inr ()))) =
        (if row = 𝔰.indexX₀ (τ (.inr ())) then (a : ℂ) else 0) +
          if row = 𝔰.besselFrame 0 then (c 0 : ℂ) else 0 := by
    have hcol : (D * Y) row (.inl (.inr ())) = D row (𝔰.indexX₀ (τ (.inr ()))) :=
      hY_col (.inl (.inr ())) row
    rw [← hcol, hD_Y]
    have h_col : (q.val * (intDiagonal l.lowestKType * C.submatrix id f)) row (.inl (.inr ())) =
        (a : ℂ) * Y row (.inl (.inr ())) + (c 0 : ℂ) * Y row (.inr 0) := by
      rw [← hq_Y, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply, mul_sum, mul_sum,
        ← sum_add_distrib]
      exact sum_congr rfl fun i _ ↦ by rw [hC_shift_inl_inr i]; ring
    rw [h_col]
    congr 1
    · by_cases h1 : row = 𝔰.indexX₀ (τ (.inr ())) <;> simp [Y, inclMatrix, Matrix.one_apply, h1]
    · by_cases h2 : row = 𝔰.besselFrame 0 <;> simp [Y, inclMatrix, Matrix.one_apply, h2]
  have hD_on_iso (b₀ : Fin 𝔰.ϱ) (row : 𝔰.BesselIndex) :
      D row (.inl b₀) =
        (if row = .inl b₀ then (a : ℂ) else 0) +
          if row = 𝔰.besselFrame b₀.succ then 1 else 0 := by
    have h_frame_cast : 𝔰.besselFrame b₀.castSucc = .inl b₀ := by simp [Shape.besselFrame, snoc]
    have hcol : (D * Y) row (.inr b₀.castSucc) = D row (𝔰.besselFrame b₀.castSucc) :=
      hY_col (.inr b₀.castSucc) row
    rw [← h_frame_cast, ← hcol, hD_Y]
    have h_col : (q.val * (intDiagonal l.lowestKType * C.submatrix id f)) row (.inr b₀.castSucc) =
        (a : ℂ) * Y row (.inr b₀.castSucc) + Y row (.inr b₀.succ) := by
      rw [← hq_Y, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply, mul_sum,
        ← sum_add_distrib]
      exact sum_congr rfl fun i _ ↦ by rw [hC_shift_inr b₀ i]; ring
    rw [h_col, h_frame_cast]
    congr 1
    by_cases h1 : row = .inl b₀ <;> simp [Y, inclMatrix, Matrix.one_apply, h_frame_cast, h1]
  have hD_adj : 𝔰.J₁ * D = Dᴴ * 𝔰.J₁ := by
    have hq_inv_gram : q⁻¹.valᴴ * signMatrix ε * q⁻¹.val = 𝔰.J₁ := gram_inv_of_gram_eq hq_gram
    have h_comm : signMatrix ε * intDiagonal l.lowestKType =
        (intDiagonal l.lowestKType)ᴴ * signMatrix ε := by
      simp [signMatrix, diagonal_conjTranspose, mul_comm]
    calc 𝔰.J₁ * D
        = (q⁻¹.valᴴ * signMatrix ε * q⁻¹.val) * (q.val * intDiagonal l.lowestKType * q⁻¹.val) := by
          rw [hq_inv_gram]
      _ = q⁻¹.valᴴ * (signMatrix ε * intDiagonal l.lowestKType) * q⁻¹.val := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc q⁻¹.val q.val, Units.inv_mul, Matrix.one_mul]
      _ = q⁻¹.valᴴ * (intDiagonal l.lowestKType)ᴴ * (q.valᴴ * 𝔰.J₁ * q.val) * q⁻¹.val := by
          rw [h_comm, hq_gram]
          simp only [Matrix.mul_assoc]
      _ = Dᴴ * 𝔰.J₁ := by
          simp only [D, conjTranspose_mul, Matrix.mul_assoc]
          rw [Units.mul_inv, Matrix.mul_one]
  have hD_eStar (b₀ : Fin 𝔰.ϱ) (col : 𝔰.BesselIndex) :
      D (eStar b₀) col =
        (if col = eStar b₀ then (a : ℂ) else 0) + 𝔰.J₁ (𝔰.besselFrame b₀.succ) col := by
    have h_lhs : (𝔰.J₁ * D) (.inl b₀) col = D (eStar b₀) col := by
      rw [Matrix.mul_apply, sum_eq_single (eStar b₀)]
      · simp
      · intro k _ hk
        rcases k with b₁ | (m₁ | b₁) <;> simp [eStar] at hk ⊢
        omega
      · exact fun h_abs ↦ absurd (mem_univ _) h_abs
    rw [← h_lhs, hD_adj, Matrix.mul_apply]
    simp only [conjTranspose_apply, hD_on_iso b₀, star_add, apply_ite star, star_natCast,
      star_zero, star_one, add_mul, sum_add_distrib]
    congr 1
    · rw [sum_eq_single (.inl b₀)]
      · rcases col with b₁ | (m₁ | b₁) <;> simp [eStar, eq_comm]
      · exact fun k _ hk ↦ by simp [hk]
      · exact fun h_abs ↦ absurd (mem_univ _) h_abs
    · rw [sum_eq_single (𝔰.besselFrame b₀.succ)]
      · simp
      · exact fun k _ hk ↦ by simp [hk]
      · exact fun h_abs ↦ absurd (mem_univ _) h_abs
  -- Subtracting `besselCharMatrix` removes all sub-level entries of `D`.
  have hD_char_tri :
      (D - besselCharMatrix (𝔰.middleGram (1 : ℂ))).BlockTriangular BesselIndex.level := by
    intro row col h_lt
    have h_ne : row ≠ col := ne_of_apply_ne BesselIndex.level h_lt.ne'
    rcases col with b₀ | (m₀ | b₀)
    · rw [Matrix.sub_apply, hD_on_iso b₀ row, ite_eq_right h_ne]
      have h_gram_zero (b' : Fin 𝔰.ϱ) :
          (𝔰.middleGram (1 : ℂ)).splitGram (𝔰.besselFrame b'.succ) (.inl b₀) = 0 := by
        simp only [Shape.besselFrame, snoc, Shape.z]
        split_ifs <;> simp [splitGram, Floors.hyperbolicGram]
      simp only [besselCharMatrix, of_apply, sum_add_distrib, h_gram_zero, ite_self, sum_const_zero,
        add_zero]
      simp [eq_comm]
    · rcases row with b₁ | (m₁ | b₁) <;>
        try (simp only [BesselIndex.level, Sum.elim_inl, Sum.elim_inr] at h_lt; omega)
      change (D - besselCharMatrix (𝔰.middleGram (1 : ℂ))) (eStar b₁) (.inr (.inl m₀)) = 0
      rw [Matrix.sub_apply, hD_eStar b₁]
      simp [besselCharMatrix, eStar]
    · rcases row with b₁ | (m₁ | b₁) <;>
        try (simp only [BesselIndex.level, Sum.elim_inl, Sum.elim_inr] at h_lt; omega)
      change (D - besselCharMatrix (𝔰.middleGram (1 : ℂ))) (eStar b₁) (eStar b₀) = 0
      rw [Matrix.sub_apply, hD_eStar b₁, ite_eq_right h_ne.symm]
      simp [besselCharMatrix, eStar]
  have h_embedH_sub_one (k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) :
      (embedH k : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1 =
        inclMatrix ℂ 𝔰.indexX₀ * ((k : Matrix 𝔰.κ 𝔰.κ ℂ) - 1) * (inclMatrix ℂ 𝔰.indexX₀)ᴴ := by
    ext (b₁ | ((k₁ | ⟨⟩) | b₁)) (b₂ | ((k₂ | ⟨⟩) | b₂)) <;>
      simp [val_toBesselH_apply_coe, inclMatrix, Matrix.mul_apply, Matrix.one_apply]
  refine ⟨x, hx_len,
    { toIsSteep := h_steep
      phase_eq := fun s ↦ ?_
      trace_eq := fun s ↦ ?_
      phase_mul := fun s₁ s₂ ↦ ?_
      re_phase_eq_zero := fun s ↦ by simp
      sign_weight_right := fun x₀ ↦ ⟨rfl, by simp [ha]⟩
      weight_nonneg_and_le := fun i _ ↦ ⟨by simp [ha]; split_ifs <;> positivity,
        fun h_impossible ↦ absurd rfl h_impossible⟩
      exists_diagonal := fun u₀ hu₀ ↦ ?_ }⟩
  · -- Phase identity: `tr (D (g - 1)) - tr (μ_u (h - 1)) = tr (besselCharMatrix (g - embedH h))`.
    have h_tr_fst : (intDiagonal l.lowestKType * (subOnePair (besselPairHom x) s).fst).trace =
        (D * ((s.val.fst : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1)).trace := by
      rw [subOnePair_besselPairHom_fst]
      change (intDiagonal l.lowestKType *
        (q⁻¹.val * ((s.val.fst : Matrix _ _ ℂ) - 1) * q.val)).trace = _
      rw [← Matrix.mul_assoc (intDiagonal l.lowestKType), trace_mul_cycle,
        ← Matrix.mul_assoc (q.val * intDiagonal l.lowestKType)]
    have h_D_indexX₀ : (inclMatrix ℂ 𝔰.indexX₀)ᴴ * D * inclMatrix ℂ 𝔰.indexX₀ =
        intDiagonal u.lowestKType := by
      have h_ne_frame (k₀ : 𝔰.κ) : 𝔰.indexX₀ k₀ ≠ 𝔰.besselFrame 0 := by
        simpa using h_frame_ne_X₀ (τ.symm k₀) 0
      ext k₁ k₂
      have h_entry : ((inclMatrix ℂ 𝔰.indexX₀)ᴴ * D * inclMatrix ℂ 𝔰.indexX₀) k₁ k₂ =
          D (𝔰.indexX₀ k₁) (𝔰.indexX₀ k₂) := by
        rw [Matrix.mul_assoc, mul_inclMatrix, Matrix.mul_apply]
        simp [inclMatrix, Matrix.one_apply]
      rw [h_entry]
      obtain ⟨x₁ | ⟨⟩, rfl⟩ := τ.surjective k₁ <;> obtain ⟨x₂ | ⟨⟩, rfl⟩ := τ.surjective k₂ <;>
        simp [hD_on_X, hD_on_unit, ha, h_ne_frame, diagonal_apply]
    have h_tr_embedH :
        (D * ((embedH s.val.snd : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1)).trace =
          (intDiagonal u.lowestKType * ((s.val.snd : Matrix 𝔰.κ 𝔰.κ ℂ) - 1)).trace := by
      rw [h_embedH_sub_one, ← Matrix.mul_assoc D, trace_mul_cycle D,
        ← Matrix.mul_assoc ((inclMatrix ℂ 𝔰.indexX₀)ᴴ * D), h_D_indexX₀]
    have h_char_diff :
        (besselCharMatrix (𝔰.middleGram (1 : ℂ)) *
          ((s.val.fst : Matrix _ _ ℂ) - (embedH s.val.snd : Matrix _ _ ℂ))).trace =
          simpleRootSum s.val.fst - conj (simpleRootSum s.val.fst) := by
      rw [Matrix.mul_sub, trace_sub, trace_besselCharMatrix_mul s.val.fst,
        trace_besselCharMatrix_mul (embedH s.val.snd),
        Filling.simpleRootSum_inv s.val.fst (besselGraph_fst_mem_besselS s),
        simpleRootSum_eq_zero_of_mem_besselH (toBesselH_mem s.val.snd),
        Filling.simpleRootSum_inv (embedH s.val.snd) (𝔰.embedH_mem_besselS s.val.snd),
        simpleRootSum_eq_zero_of_mem_besselH (toBesselH_mem s.val.snd)]
      simp [sub_eq_add_neg]
    have h_zero := besselGraph_trace_mul_sub_eq_zero s hD_char_tri
    have h_sub_id : ((s.val.fst : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1) -
        ((embedH s.val.snd : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1) =
        (s.val.fst : Matrix _ _ ℂ) - (embedH s.val.snd : Matrix _ _ ℂ) := by abel
    rw [HCParam.phase, h_tr_fst, subOnePair_besselPairHom_snd, ← h_tr_embedH, ← trace_sub,
      ← Matrix.mul_sub, h_sub_id]
    rw [Matrix.sub_mul, trace_sub, sub_eq_zero] at h_zero
    rw [h_zero, h_char_diff]
  · -- Trace equality: apply `besselGraph_trace_mul_sub_eq_zero` to `M = 1`.
    rw [subOnePair_besselPairHom_fst, subOnePair_besselPairHom_snd]
    change (q⁻¹.val * ((s.val.fst : Matrix _ _ ℂ) - 1) * q.val).trace = _
    rw [trace_mul_cycle, Units.mul_inv, Matrix.one_mul]
    have h_zero := besselGraph_trace_mul_sub_eq_zero s blockTriangular_one
    rw [Matrix.one_mul] at h_zero
    have h_inc_iso : (inclMatrix ℂ 𝔰.indexX₀)ᴴ * inclMatrix ℂ 𝔰.indexX₀ = 1 := by
      ext k₁ k₂; simp [inclMatrix, Matrix.mul_apply, Matrix.one_apply, eq_comm]
    have h_embed : ((embedH s.val.snd : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1).trace =
        ((s.val.snd : Matrix 𝔰.κ 𝔰.κ ℂ) - 1).trace := by
      rw [h_embedH_sub_one, trace_mul_cycle, h_inc_iso, Matrix.one_mul]
    rw [← h_embed, ← sub_eq_zero, ← trace_sub]
    simpa [sub_sub_sub_cancel_right] using h_zero
  · -- Additivity of `simpleRootSum - conj simpleRootSum` on `besselGraph`.
    have h_mul := simpleRootSum_mul (besselGraph_fst_mem_besselS s₁)
      (besselGraph_fst_mem_besselS s₂)
    change simpleRootSum (s₁.val.fst * s₂.val.fst) -
      conj (simpleRootSum (s₁.val.fst * s₂.val.fst)) = _
    rw [h_mul, map_add]
    ring
  · -- Diagonal copy of `U(X)`.
    obtain ⟨k₀, hk₀⟩ := exists_unitary_sub_one_eq_inclMatrix (ε := (1 : 𝔰.κ → ℤˣ)) τ
      (fun _ ↦ rfl) (mem_unitaryGroup_iff'.1 hu₀)
    have h1 : signMatrix (1 : 𝔰.κ → ℤˣ) = (1 : Matrix 𝔰.κ 𝔰.κ ℂ) := by simp [signMatrix]
    let k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) := ⟨k₀.val, h1 ▸ k₀.property⟩
    let s₀ : 𝔰.besselGraph := 𝔰.besselGraphChart (1, k)
    have hs₀_fst : s₀.val.fst = embedH k := by simp [s₀]
    have hs₀_snd : (s₀.val.snd : Matrix 𝔰.κ 𝔰.κ ℂ) = (k₀ : Matrix 𝔰.κ 𝔰.κ ℂ) := rfl
    refine ⟨s₀, ?_⟩
    rw [Prod.ext_iff, subOnePair_besselPairHom_fst, subOnePair_besselPairHom_snd, hs₀_snd, hk₀]
    refine ⟨?_, rfl⟩
    change q⁻¹.val * ((s₀.val.fst : Matrix _ _ ℂ) - 1) * q.val = _
    rw [hs₀_fst, h_embedH_sub_one k]
    have hk_val : (k : Matrix 𝔰.κ 𝔰.κ ℂ) - 1 =
        inclMatrix ℂ (τ ∘ Sum.inl) * (u₀ - 1) * (inclMatrix ℂ (τ ∘ Sum.inl))ᴴ := hk₀
    have h_comp_inc : inclMatrix ℂ 𝔰.indexX₀ * inclMatrix ℂ (τ ∘ Sum.inl) =
        inclMatrix ℂ (𝔰.indexX₀ ∘ τ ∘ Sum.inl) := by
      ext row x₀; simp [inclMatrix, Matrix.mul_apply, Matrix.one_apply]
    have h_embed_inc : inclMatrix ℂ 𝔰.indexX₀ * ((k : Matrix 𝔰.κ 𝔰.κ ℂ) - 1) *
        (inclMatrix ℂ 𝔰.indexX₀)ᴴ =
          inclMatrix ℂ (𝔰.indexX₀ ∘ τ ∘ Sum.inl) * (u₀ - 1) *
            (inclMatrix ℂ (𝔰.indexX₀ ∘ τ ∘ Sum.inl))ᴴ := by
      rw [hk_val, ← Matrix.mul_assoc (inclMatrix ℂ 𝔰.indexX₀),
        ← Matrix.mul_assoc (inclMatrix ℂ 𝔰.indexX₀), h_comp_inc, Matrix.mul_assoc,
        ← conjTranspose_mul, h_comp_inc, Matrix.mul_assoc]
    have hq_inc : q.val * inclMatrix ℂ (e ∘ Sum.inl) =
        inclMatrix ℂ (𝔰.indexX₀ ∘ τ ∘ Sum.inl) := by
      ext row x₀
      have h_col := congrFun₂ hq_Y row (.inl (.inl x₀))
      have hC_col (i : 𝔰.BesselIndex) :
          C.submatrix id f i (.inl (.inl x₀)) = inclMatrix ℂ (e ∘ Sum.inl) i x₀ := by
        obtain ⟨x₁ | i₁, rfl⟩ := e.surjective i <;>
          simp [C, C₀, f, inclMatrix, Matrix.one_apply]
      rw [Matrix.mul_apply]
      simp_rw [← hC_col]
      rw [← Matrix.mul_apply, h_col]
      by_cases h1 : row = 𝔰.indexX₀ (τ (.inl x₀)) <;>
        simp [Y, inclMatrix, Matrix.one_apply, h1]
    have hq_inv_inc : q⁻¹.val * inclMatrix ℂ (𝔰.indexX₀ ∘ τ ∘ Sum.inl) =
        inclMatrix ℂ (e ∘ Sum.inl) := by
      rw [← hq_inc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have h_inc_q : (inclMatrix ℂ (𝔰.indexX₀ ∘ τ ∘ Sum.inl))ᴴ * q.val =
        (inclMatrix ℂ (e ∘ Sum.inl))ᴴ := by
      have hJ_inc : (inclMatrix ℂ (𝔰.indexX₀ ∘ τ ∘ Sum.inl))ᴴ * 𝔰.J₁ =
          (inclMatrix ℂ (𝔰.indexX₀ ∘ τ ∘ Sum.inl))ᴴ := by
        ext x₀ (b₂ | ((k₂ | ⟨⟩) | b₂)) <;>
          simp [inclMatrix, splitGram, middleGram, Matrix.mul_apply, Matrix.one_apply, eq_comm]
      have hsgn_inc : (inclMatrix ℂ (e ∘ Sum.inl))ᴴ * signMatrix ε =
          (inclMatrix ℂ (e ∘ Sum.inl))ᴴ := by
        ext x₀ col
        rw [signMatrix, mul_diagonal]
        rcases eq_or_ne col (e (.inl x₀)) with rfl | hne
        · simp [inclMatrix, h_steep.sign_inl]
        · simp [inclMatrix, hne]
      calc (inclMatrix ℂ (𝔰.indexX₀ ∘ τ ∘ Sum.inl))ᴴ * q.val
          = (q.val * inclMatrix ℂ (e ∘ Sum.inl))ᴴ * 𝔰.J₁ * q.val := by rw [← hJ_inc, ← hq_inc]
        _ = (inclMatrix ℂ (e ∘ Sum.inl))ᴴ * (q.valᴴ * 𝔰.J₁ * q.val) := by simp [Matrix.mul_assoc]
        _ = (inclMatrix ℂ (e ∘ Sum.inl))ᴴ := by rw [hq_gram, hsgn_inc]
    calc q⁻¹.val * (inclMatrix ℂ 𝔰.indexX₀ * ((k : Matrix 𝔰.κ 𝔰.κ ℂ) - 1) *
            (inclMatrix ℂ 𝔰.indexX₀)ᴴ) * q.val
        = q⁻¹.val * (inclMatrix ℂ (𝔰.indexX₀ ∘ τ ∘ Sum.inl) * (u₀ - 1) *
            (inclMatrix ℂ (𝔰.indexX₀ ∘ τ ∘ Sum.inl))ᴴ) * q.val := by rw [h_embed_inc]
      _ = (q⁻¹.val * inclMatrix ℂ (𝔰.indexX₀ ∘ τ ∘ Sum.inl)) * (u₀ - 1) *
            ((inclMatrix ℂ (𝔰.indexX₀ ∘ τ ∘ Sum.inl))ᴴ * q.val) := by
          simp only [Matrix.mul_assoc]
      _ = inclMatrix ℂ (e ∘ Sum.inl) * (u₀ - 1) * (inclMatrix ℂ (e ∘ Sum.inl))ᴴ := by
          rw [hq_inv_inc, h_inc_q]

/-- Split the coordinates of `G₁` into `X` and `2 n` more (by `e`), and those of `H` into `X` and
one more (by `τ`). Let the parameter `l` of `U(ε)` be steep with bound `B ≥ 1` (its lowest `K`-type
has weight `0` on `X` and decreasing weight in `[-3 B, -B]` on the others, where the signs
alternate), and let the lowest `K`-type of the parameter `u` of `H` have weight `a` at the last
coordinate and `0` on `X`. Let both parameters have entries of modulus at most `L` and large gap
(`HasLargeGap`: for `2λ` with `N` coordinates, entries of `λ` at coordinates of opposite sign differ
by at least `500 N³ + excess`), where `10 ^ 30 ((r + k)² log β)³ ≤ excess`. If `10 ^ 12 ≤ β`,
`r + k + L ≤ β`, `3 B + a ≤ b ^ 2` and `8 n r ≤ b`, there is a point `x` whose length
`besselLength x`, the infimum of `‖s x‖ + 1` over `s` in `R`, is at most `b ^ (5 n)`, and such that
the volume of `{‖x⁻¹ s x - 1‖ ≤ 1}` in `R` is at most `β ^ (20 (r + k)²)` times the modulus of the
period. The period is the integral over `s` in `R`, with image `t` in `H`, of `c_l(x⁻¹ s x)` times
the conjugate of `c_u(t)` times `exp (conj σ - σ)`. Here `c_l = l.dsCoeff` and `c_u = u.dsCoeff` are
the discrete series coefficients, and `σ = simpleRootSum s` is the sum of the entries of `s` just
above the diagonal on the frame `e₁, …, e_ϱ, z`. -/
theorem IsSteep.exists_stationary_point {X : Type} [Fintype X] {l : HCParam ε}
    {u : HCParam (1 : 𝔰.κ → ℤˣ)} {e : X ⊕ Fin (2 * 𝔰.ϱ + 2) ≃ 𝔰.BesselIndex} {B b β : ℝ}
    {a L excess : ℕ} (h_steep : IsSteep l B e) (τ : X ⊕ Unit ≃ 𝔰.κ)
    (ha : ∀ i : 𝔰.κ, u.lowestKType i = if i = τ (Sum.inr ()) then (a : ℤ) else 0)
    (hB : 1 ≤ B) (hb : 3 * B + a ≤ b ^ 2) (hb_rank : 8 * 𝔰.n * 𝔰.r ≤ b)
    (hl : l.HasLargeGap excess) (hu : u.HasLargeGap excess)
    (hL : ∀ i : 𝔰.BesselIndex, |l i| ≤ L) (hK : ∀ i : 𝔰.κ, |u i| ≤ L)
    (hβ : 10 ^ 12 ≤ β) (h_rank : 𝔰.r + 𝔰.k + L ≤ β)
    (h_excess : 10 ^ 30 * ((𝔰.r + 𝔰.k) ^ 2 * β.log) ^ 3 ≤ excess) :
    ∃ x : 𝔰.G₁,
      besselLength x ≤ b ^ (5 * 𝔰.n) ∧
      𝔰.besselGraphMeasure.real
          {s : 𝔰.besselGraph | ‖(subOnePair (besselPairHom (ε := ε) x) s).fst‖ ≤ 1} ≤
        β ^ (20 * (𝔰.r + 𝔰.k) ^ 2) *
          ‖∫ s : 𝔰.besselGraph, l.laplaceIntegrand u (besselPairHom x)
            (fun s' : 𝔰.besselGraph ↦ simpleRootSum s'.val.fst - conj (simpleRootSum s'.val.fst)) s
            ∂𝔰.besselGraphMeasure‖ := by
  classical
  have : MeasurableMul 𝔰.besselGraph := measurableMul_besselGraph
  have : BorelSpace 𝔰.besselGraph := borelSpace_besselGraph
  have : 𝔰.besselGraphMeasure.IsMulRightInvariant := 𝔰.besselGraphMeasure_isMulRightInvariant
  have : IsFiniteMeasureOnCompacts 𝔰.besselGraphMeasure :=
    𝔰.besselGraphMeasure_finiteOnCompacts
  have : Nonempty 𝔰.κ := ⟨τ (Sum.inr ())⟩
  -- Build the stationary point `x` directly from the Lagrange/Vandermonde frame on the `2 n`
  -- coordinates of `G₁` and one coordinate of `H` outside `X`, with `besselLength x ≤ b ^ (5 n)`
  -- and `besselPairHom x` satisfying `IsLaplaceDatum` for the Bessel character phase.
  obtain ⟨x, hx_len, h_datum⟩ :=
    h_steep.exists_isLaplaceDatum_besselPairHom τ ha hB hb hb_rank
  -- The first component `s ↦ x⁻¹ s x` of `besselPairHom x` is proper and the second component
  -- `s ↦ h` is continuous, so `IsLaplaceDatum.laplace_method` bounds the volume of the set where
  -- both components have norm at most `β + 1` by `β ^ (20 (r + k)²) * ‖period‖`.
  have hj_cont : Continuous fun s : 𝔰.besselGraph ↦ (besselPairHom (ε := ε) x s).snd := by
    simp only [continuous_U_iff_matrix, besselPairHom_snd_val]
    exact Units.continuous_val.comp (continuous_subtypeVal.comp
      (continuous_snd.comp continuous_subtypeVal))
  obtain ⟨-, h_period⟩ := h_datum.laplace_method 𝔰.besselGraphMeasure
    (isProperMap_besselPairHom_fst x) hj_cont hl hu hB hL hK hβ h_rank h_excess
  -- The unit ball `{‖x⁻¹ s x - 1‖ ≤ 1}` lies in `{‖x⁻¹ s x‖ ≤ β + 1 ∧ ‖h‖ ≤ β + 1}`, as `H` is
  -- compact (`‖h‖ = 1`).
  have hβ_one : 1 ≤ β := le_trans (by norm_num) hβ
  have h_ball : {s : 𝔰.besselGraph | ‖(subOnePair (besselPairHom (ε := ε) x) s).fst‖ ≤ 1} ⊆
      {s : 𝔰.besselGraph |
        ‖((besselPairHom (ε := ε) x s).fst : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖ ≤ β + 1 ∧
          ‖((besselPairHom (ε := ε) x s).snd : Matrix 𝔰.κ 𝔰.κ ℂ)‖ ≤ β + 1} := by
    refine fun s hs ↦ ⟨(norm_le_insert' _ 1).trans (add_le_add (norm_one.trans_le hβ_one) hs), ?_⟩
    rw [besselPairHom_snd_val, CStarRing.norm_of_mem_unitary (U_one_mem_unitaryGroup s.val.snd)]
    linarith
  exact ⟨x, hx_len,
    ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (pow_nonneg (zero_le_one.trans hβ_one) _) (norm_nonneg _))
      ((measure_mono h_ball).trans h_period)⟩

end DiscreteSeries

end New

/-! ## The Bessel integral -/

namespace New.DiscreteSeries

open Matrix Fintype Complex Norms.L2Operator MeasureTheory ComplexConjugate ENNReal HCParam
  InnerProductSpace ContinuousLinearMap

variable {𝔰 : Shape} {I : Type*} {ε : 𝔰.BesselIndex → ℤˣ} [Fintype I] [DecidableEq I]
  [UnitarySignFrame 𝔰 ε]

private lemma sFinite_besselGraphMeasure : SFinite 𝔰.besselGraphMeasure :=
  @Measure.instSFiniteMap _ _ _ _ (𝔰.besselHaar.prod volume) 𝔰.besselGraphChart inferInstance

private lemma continuous_sum_finset {α β ι : Type*} [TopologicalSpace α] [AddCommMonoid β]
    [TopologicalSpace β] [ContinuousAdd β] (s : Finset ι) {f : ι → α → β}
    (hf : ∀ i ∈ s, Continuous (f i)) : Continuous fun a ↦ ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact continuous_const
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).fun_add
      (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

private lemma continuous_uncurry_smul_mul_left {G S E : Type*} [TopologicalSpace G] [Mul G]
    [ContinuousMul G] [TopologicalSpace S] [TopologicalSpace E] [SMul ℂ E] [ContinuousSMul ℂ E]
    {k : G → ℂ} {F : G → S → E} (hk : Continuous k) (hF : Continuous F.uncurry) (y : G) :
    Continuous (Function.uncurry fun (a : G) (s : S) ↦ k a • F (y * a) s) :=
  (hk.comp continuous_fst).smul
    (hF.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd))

/-- The map `(y, s) ↦ s y` carries the measures of 𝖴∖G₁ and of the Bessel group `R = 𝖴 H` to the
Haar measure of G₁. -/
lemma measurePreserving_unfold_besselGraphMeasure :
    MeasurePreserving (fun q : 𝔰.G₁ × 𝔰.besselGraph ↦ q.snd.val.fst * q.fst)
      (besselQuotMeasure.prod 𝔰.besselGraphMeasure) volume := by
  have : SFinite 𝔰.besselGraphMeasure := sFinite_besselGraphMeasure
  have h_meas : Measurable (fun q : 𝔰.G₁ × 𝔰.besselGraph ↦ q.snd.val.fst * q.fst) :=
    (measurable_fst.comp (measurable_subtypeVal.comp measurable_snd)).mul measurable_fst
  refine ⟨h_meas, Measure.ext_of_lintegral _ fun (g : 𝔰.G₁ → ℝ≥0∞) (hg : Measurable g) ↦ ?_⟩
  rw [lintegral_map hg h_meas,
    lintegral_prod (fun q : 𝔰.G₁ × 𝔰.besselGraph ↦ g (q.snd.val.fst * q.fst))
      (hg.comp h_meas).aemeasurable,
    lintegral_unfold_besselGraphMeasure (x := 1) g hg]
  simp only [one_mul]

variable (l : HCParam ε) (rep : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ) →* unitaryGroup I ℂ) (x : 𝔰.G₁)
  (v : EuclideanSpace ℂ I)

/-- The volume of the set of `s` in `R` with `‖x⁻¹ s x - 1‖ ≤ 1`, the matrix `x⁻¹ s x` being written
in the frame of signs `ε` (the first component of `besselPairHom x s`). -/
noncomputable def besselBallVolume : ℝ≥0∞ :=
  𝔰.besselGraphMeasure {s : 𝔰.besselGraph |
    ‖((besselPairHom (ε := ε) x s).fst : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) - 1‖ ≤ 1}

/-- The ball whose volume is `besselBallVolume x` has finite measure, as the conjugation by `x` is
proper on `R`. -/
lemma besselBallVolume_ne_top : besselBallVolume (ε := ε) x ≠ ∞ := by
  have : MeasurableMul 𝔰.besselGraph := measurableMul_besselGraph
  have : 𝔰.besselGraphMeasure.IsMulRightInvariant := 𝔰.besselGraphMeasure_isMulRightInvariant
  have : IsFiniteMeasureOnCompacts 𝔰.besselGraphMeasure := 𝔰.besselGraphMeasure_finiteOnCompacts
  exact measure_ball_ne_top_of_isProperMap 𝔰.besselGraphMeasure
    (j := (MonoidHom.fst _ _).comp (besselPairHom x)) (isProperMap_besselPairHom_fst x) 1

/-- The ball whose volume is `besselBallVolume x` has nonzero measure, as it is a neighbourhood of
`1` in `R`. -/
lemma besselBallVolume_ne_zero : besselBallVolume (ε := ε) x ≠ 0 := by
  have h_cont : Continuous fun s : 𝔰.besselGraph ↦ (besselPairHom (ε := ε) x s).fst :=
    (isProperMap_besselPairHom_fst x).continuous
  exact measure_sublevel_ne_zero 𝔰.besselGraphMeasure
    (by rw [map_one]; simp only [Prod.fst_one, OneMemClass.coe_one, Units.val_one, sub_self,
      norm_zero, zero_lt_one])
    (((Units.continuous_val.comp (continuous_subtypeVal.comp h_cont)).fun_sub
      continuous_const).norm)

/-- The covering bound: let `N = 9 r ^ 2`. The integral of `(2 / ‖x⁻¹ s y‖) ^ N` over `s` in
`besselGraph` (the group `R`) is at most `16 ^ N` times `besselBallVolume x`, uniformly in `y`. The
norm is the operator norm in the frame of signs `ε` (via `frameEquiv`). -/
lemma lintegral_decay_le_besselBallVolume (y : 𝔰.G₁) :
    ∫⁻ s : 𝔰.besselGraph,
        .ofReal ((2 / ‖(frameEquiv (ε := ε) (x⁻¹ * (s.val.fst * y)) :
          Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖) ^ (9 * 𝔰.r ^ 2))
        ∂𝔰.besselGraphMeasure ≤
      .ofReal (16 ^ (9 * 𝔰.r ^ 2)) * besselBallVolume (ε := ε) x := by
  have : MeasurableMul 𝔰.besselGraph := measurableMul_besselGraph
  have : 𝔰.besselGraphMeasure.IsMulRightInvariant := 𝔰.besselGraphMeasure_isMulRightInvariant
  have : IsFiniteMeasureOnCompacts 𝔰.besselGraphMeasure := 𝔰.besselGraphMeasure_finiteOnCompacts
  have : BorelSpace 𝔰.besselGraph := borelSpace_besselGraph
  let j : 𝔰.besselGraph →* USign ε := (MonoidHom.fst _ _).comp (besselPairHom x)
  have hj_apply (s : 𝔰.besselGraph) : j s = frameEquiv (x⁻¹ * s.val.fst * x) := rfl
  -- The general covering bound for the proper map `j`, at the point `x⁻¹ y`.
  have hr : 0 < 𝔰.r ^ 2 := pow_pos Fintype.card_pos 2
  refine (lintegral_decay_le 𝔰.besselGraphMeasure (j := j) (isProperMap_besselPairHom_fst x)
    (by dsimp only [Shape.r] at hr ⊢; omega) (frameEquiv (x⁻¹ * y))).trans_eq' ?_
  refine lintegral_congr fun s ↦ ?_
  rw [hj_apply, show frameEquiv (ε := ε) (x⁻¹ * s.val.fst * x) * frameEquiv (ε := ε) (x⁻¹ * y) =
      frameEquiv (ε := ε) (x⁻¹ * (s.val.fst * y)) from
    (frameEquiv.map_mul _ _).symm.trans (congrArg frameEquiv (by
      rw [mul_assoc, mul_assoc, mul_inv_cancel_left]))]

variable {l rep v} {excess : ℕ}

/-- If `l` has the gap `500 r ^ 3 + excess` (`HasLargeGap`), its coefficient `c_λ`, which is
`l.dsCoeffInFrame`, satisfies `|c_λ(g)| ≤ (2 / ‖g‖) ^ (j + 9 r ^ 2)` for `j ≤ excess`, the norm
being read in the frame of signs `ε`. -/
lemma norm_dsCoeffInFrame_le (h_gap : l.HasLargeGap excess) {j : ℕ} (hj : j ≤ excess) (g : 𝔰.G₁) :
    ‖l.dsCoeffInFrame g‖ ≤
      (2 / ‖(frameEquiv (ε := ε) g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ)‖) ^
        (j + 9 * 𝔰.r ^ 2) := by
  have h_sq : 𝔰.r ^ 2 ≤ 𝔰.r ^ 3 := pow_le_pow_right₀ Fintype.card_pos (by omega)
  have h_exponent : j + 9 * 𝔰.r ^ 2 ≤ gapThreshold 𝔰.BesselIndex excess := by
    dsimp only [gapThreshold, Shape.r] at h_sq ⊢
    omega
  exact norm_dsCoeff_le_pow h_gap (mod_cast h_exponent) _

/-- For a continuous representation `rep`, the integrand `besselIntegrand l rep x v y s`, which is
`c_λ(x⁻¹ s y) π(s)⁻¹ v` with `c_λ = l.dsCoeffInFrame`, is jointly continuous in `y` and `s`. -/
lemma continuous_besselIntegrand (h_cont : Continuous rep) :
    Continuous (besselIntegrand l rep x v).uncurry := by
  have : ContinuousMul 𝔰.G₁ := continuousMul_G₁
  change Continuous fun q : 𝔰.G₁ × 𝔰.besselGraph ↦
    l.dsCoeffInFrame (x⁻¹ * (q.snd.val.fst * q.fst)) •
      wave (-simpleRootSum q.snd.val.fst) • WithLp.toLp 2 ((rep q.snd.val.snd⁻¹).val *ᵥ v.ofLp)
  have h_fst : Continuous fun q : 𝔰.G₁ × 𝔰.besselGraph ↦ q.snd.val.fst :=
    continuous_fst.comp (continuous_subtypeVal.comp continuous_snd)
  have h_snd : Continuous fun q : 𝔰.G₁ × 𝔰.besselGraph ↦ q.snd.val.snd :=
    continuous_snd.comp (continuous_subtypeVal.comp continuous_snd)
  have h1 : Continuous fun q : 𝔰.G₁ × 𝔰.besselGraph ↦
      l.dsCoeffInFrame (x⁻¹ * (q.snd.val.fst * q.fst)) :=
    continuous_dsCoeffInFrame.comp (continuous_const.fun_mul (h_fst.fun_mul continuous_fst))
  have h_mat : Continuous fun q : 𝔰.G₁ × 𝔰.besselGraph ↦
      (q.snd.val.fst : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) :=
    Units.continuous_val.comp (continuous_subtypeVal.comp h_fst)
  have h_srs : Continuous fun q : 𝔰.G₁ × 𝔰.besselGraph ↦ simpleRootSum q.snd.val.fst :=
    continuous_sum_finset _ fun a _ ↦
      (continuous_apply _).comp ((continuous_apply _).comp h_mat)
  have h2 : Continuous fun q : 𝔰.G₁ × 𝔰.besselGraph ↦ wave (-simpleRootSum q.snd.val.fst) :=
    Complex.continuous_exp.comp (h_srs.neg.fun_sub (Complex.continuous_conj.comp h_srs.neg))
  have h_rep : Continuous fun q : 𝔰.G₁ × 𝔰.besselGraph ↦ (rep q.snd.val.snd⁻¹).val :=
    continuous_subtypeVal.comp (h_cont.comp h_snd.inv)
  have h3 : Continuous fun q : 𝔰.G₁ × 𝔰.besselGraph ↦
      WithLp.toLp 2 ((rep q.snd.val.snd⁻¹).val *ᵥ v.ofLp) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦
      continuous_sum_finset _ fun j _ ↦
        ((continuous_apply j).comp ((continuous_apply i).comp h_rep)).fun_mul continuous_const)
  exact h1.fun_smul (h2.fun_smul h3)

/-- For a unit vector `v`, the norm of the integrand `c_λ(x⁻¹ s y) π(s)⁻¹ v` is `|c_λ(x⁻¹ s y)|`,
as `π` is unitary. -/
lemma enorm_besselIntegrand (hv_norm : ‖v‖ = 1) (y : 𝔰.G₁) (s : 𝔰.besselGraph) :
    ‖besselIntegrand l rep x v y s‖ₑ = ‖l.dsCoeffInFrame (x⁻¹ * (s.val.fst * y))‖ₑ := by
  rw [besselIntegrand, ← ofReal_norm, norm_smul, norm_smul, norm_wave, one_mul,
    Unitary.norm_map, hv_norm, mul_one, ofReal_norm]

/-- For a unit vector `v` and a parameter `l` of gap `500 r³ + excess`, the integral over `R` of the
norm of `besselIntegrand l rep x v y` is at most `16 ^ (9 r ^ 2)` times `besselBallVolume x`, the
volume of `{‖x⁻¹ s x - 1‖ ≤ 1}` in `R`. -/
lemma lintegral_enorm_besselIntegrand_le (hv_norm : ‖v‖ = 1) (h_gap : l.HasLargeGap excess)
    (y : 𝔰.G₁) :
    ∫⁻ s : 𝔰.besselGraph, ‖besselIntegrand l rep x v y s‖ₑ ∂𝔰.besselGraphMeasure ≤
      .ofReal (16 ^ (9 * 𝔰.r ^ 2)) * besselBallVolume (ε := ε) x := by
  refine (lintegral_mono fun s ↦ ?_).trans (lintegral_decay_le_besselBallVolume x y)
  rw [enorm_besselIntegrand x hv_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (by
    simpa only [zero_add] using norm_dsCoeffInFrame_le h_gap (Nat.zero_le excess) _)

/-- For a continuous representation `rep`, a unit vector `v` and a parameter `l` of gap
`500 r³ + excess`, the integral over `R` defining `besselAverage l rep x v y` converges
absolutely. -/
lemma integrable_besselIntegrand (h_cont : Continuous rep) (hv_norm : ‖v‖ = 1)
    (h_gap : l.HasLargeGap excess) (y : 𝔰.G₁) :
    Integrable (besselIntegrand l rep x v y) 𝔰.besselGraphMeasure :=
  ⟨((continuous_besselIntegrand x h_cont).uncurry_left y).aestronglyMeasurable,
    (lintegral_enorm_besselIntegrand_le x hv_norm h_gap y).trans_lt
      (mul_lt_top ofReal_lt_top (besselBallVolume_ne_top x).lt_top)⟩

private lemma besselValueRep_mul_val (k₁ k₂ : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) (w : EuclideanSpace ℂ I) :
    (besselValueRep rep (k₁ * k₂)).val w =
      (besselValueRep rep k₁).val ((besselValueRep rep k₂).val w) := by
  rw [(besselValueRep rep).map_mul k₁ k₂, Submonoid.coe_mul, mul_apply_eq_comp]

private lemma besselValueRep_inv_val (k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ)) :
    (besselValueRep rep k⁻¹).val = ContinuousLinearMap.adjoint (besselValueRep rep k).val := by
  have hBA : (besselValueRep rep k⁻¹).val * (besselValueRep rep k).val = 1 := by
    have h : besselValueRep rep k⁻¹ * besselValueRep rep k = 1 := by
      rw [← (besselValueRep rep).map_mul, inv_mul_cancel, (besselValueRep rep).map_one]
    exact congrArg Subtype.val h
  exact left_inv_eq_right_inv hBA (besselValueRep rep k).2.2

/-- Let `rep` be a continuous unitary representation of `H` on `ℂ^I`, `v` a unit vector of `ℂ^I`,
`x` a point of `G₁`, and `l = 2λ` a parameter with coefficient `c_λ = l.dsCoeffInFrame` and large
gap. For `s = (g, h)` in `R` let `π(s)` be the scalar `wave (simpleRootSum g)` times the operator
`besselValueRep rep h` of `rep h`. Let `W = besselAverage l rep x v`, that is,
`W(y) = ∫_R c_λ(x⁻¹ t y) π(t)⁻¹ v dt` for the measure `du dh` on `R = 𝖴 H`. Then
`W(s y) = π(s) W(y)` for all `s` in `R` and `y` in `G₁`. -/
lemma besselAverage_mul (h_cont : Continuous rep) (hv_norm : ‖v‖ = 1)
    (h_gap : l.HasLargeGap excess) (s : 𝔰.besselGraph) (y : 𝔰.G₁) :
    besselAverage l rep x v (s.val.fst * y) =
      wave (simpleRootSum s.val.fst) •
        (besselValueRep rep s.val.snd).val (besselAverage l rep x v y) := by
  have : MeasurableMul 𝔰.besselGraph := measurableMul_besselGraph
  have : 𝔰.besselGraphMeasure.IsMulRightInvariant := 𝔰.besselGraphMeasure_isMulRightInvariant
  -- Substitute `t * s⁻¹` for `t`; the measure is right invariant and `simpleRootSum` is additive.
  have h_wave (t : 𝔰.besselGraph) : wave (-simpleRootSum (t.val.fst * s.val.fst⁻¹)) =
      wave (simpleRootSum s.val.fst) * wave (-simpleRootSum t.val.fst) := by
    rw [simpleRootSum_mul (besselGraph_fst_mem_besselS t) (inv_mem (besselGraph_fst_mem_besselS s)),
      Filling.simpleRootSum_inv s.val.fst (besselGraph_fst_mem_besselS s), wave, wave, wave,
      ← Complex.exp_add]
    congr 1
    simp only [map_neg, map_add, neg_add, neg_neg]
    ring
  have h_point (t : 𝔰.besselGraph) : besselIntegrand l rep x v (s.val.fst * y) (t * s⁻¹) =
      wave (simpleRootSum s.val.fst) •
        (besselValueRep rep s.val.snd).val (besselIntegrand l rep x v y t) := by
    dsimp only [besselIntegrand]
    have h_fst : (t * s⁻¹ : 𝔰.besselGraph).val.fst = t.val.fst * s.val.fst⁻¹ := rfl
    have h_snd : ((t * s⁻¹ : 𝔰.besselGraph).val.snd)⁻¹ = s.val.snd * t.val.snd⁻¹ := by
      change (t.val.snd * s.val.snd⁻¹)⁻¹ = _
      rw [_root_.mul_inv_rev, inv_inv]
    rw [h_fst, h_snd, mul_assoc t.val.fst, inv_mul_cancel_left, h_wave t,
      besselValueRep_mul_val, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul,
      smul_smul, smul_smul, smul_smul]
    refine congrArg (· • _) ?_
    ring
  rw [besselAverage, besselAverage, ← integral_mul_right_eq_self _ s⁻¹, funext h_point,
    integral_smul, integral_comp_comm _ (integrable_besselIntegrand x h_cont hv_norm h_gap y)]

/-- Let `rep` be a continuous unitary representation of `H`, `v` a unit vector, and `l = 2λ` a
parameter with coefficient `c_λ = l.dsCoeffInFrame` and large gap. Let `π` be the representation of
`R = 𝖴 H` that is `rep` on `H` and the character `ψ(u) = exp (σ - conj σ)`, `σ = simpleRootSum u`,
on the unipotent group `𝖴`. Then `W = besselAverage l rep x v`, given by
`W(y) = ∫_R c_λ(x⁻¹ s y) π(s)⁻¹ v ds`, is a Bessel function: it is bounded and measurable, with
`W(u y) = ψ(u) W(y)` for `u` in `𝖴` and `W(h y) = rep h W(y)` for `h` in `H`. -/
lemma isBesselFunction_besselAverage (h_cont : Continuous rep) (hv_norm : ‖v‖ = 1)
    (h_gap : l.HasLargeGap excess) : IsBesselFunction rep (besselAverage l rep x v) where
  stronglyMeasurable := by
    have : SFinite 𝔰.besselGraphMeasure := sFinite_besselGraphMeasure
    exact (continuous_besselIntegrand x h_cont).stronglyMeasurable.integral_prod_right
  bounded :=
    have h_le (y : 𝔰.G₁) : ‖besselAverage l rep x v y‖ₑ ≤
        .ofReal (16 ^ (9 * 𝔰.r ^ 2)) * besselBallVolume (ε := ε) x :=
      (eNorm_integral_le_lintegral_eNorm _).trans
        (lintegral_enorm_besselIntegrand_le x hv_norm h_gap y)
    ⟨_, fun y ↦ toReal_mono (mul_ne_top ofReal_ne_top (besselBallVolume_ne_top x)) (h_le y)⟩
  map_unipotent_mul s hs y := by
    have h := besselAverage_mul x h_cont hv_norm h_gap (𝔰.besselGraphChart ⟨⟨s, hs⟩, 1⟩) y
    simp only [Shape.besselGraphChart_apply_coe, map_one, one_mul, OneMemClass.coe_one,
      one_apply_eq_self] at h
    exact h
  map_unitary_mul k y := by
    have h := besselAverage_mul x h_cont hv_norm h_gap (𝔰.besselGraphChart ⟨1, k⟩) y
    simp only [Shape.besselGraphChart_apply_coe, OneMemClass.coe_one, mul_one,
      simpleRootSum_eq_zero_of_mem_besselH (toBesselH_mem k), wave, map_zero, sub_self,
      Complex.exp_zero, one_smul] at h
    exact h

/-- Let `rep` be a continuous unitary representation of `H` on `ℂ^I`, `v` a unit vector of `ℂ^I`,
`x` a point of `G₁`, and `l = 2λ` a parameter with coefficient `c_λ = l.dsCoeffInFrame`, formal
degree `deg` and large gap. Let `W = besselAverage l rep x v`. Then convolution with the idempotent
kernel `e_λ = deg c_λ` reproduces `W`: `∫ e_λ(a⁻¹) W(y a) da = W(y)` for all `y` in `G₁`. -/
lemma convolve_besselAverage (h_cont : Continuous rep) (hv_norm : ‖v‖ = 1)
    (h_gap : l.HasLargeGap excess) :
    convolve (besselAverage l rep x v) (fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) =
      besselAverage l rep x v := by
  have : ContinuousMul 𝔰.G₁ := continuousMul_G₁
  have : ContinuousInv 𝔰.G₁ := continuousInv_G₁
  have : SFinite 𝔰.besselGraphMeasure := sFinite_besselGraphMeasure
  -- Exchange the two integrals and use the product formula of the kernel `deg * c_λ`.
  have h_kernel : IsIdempotentKernel fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g :=
    isIdempotentKernel_dsCoeffInFrame h_gap
  have h_reprod (g : 𝔰.G₁) :
      ∫ a : 𝔰.G₁, l.formalDegree * l.dsCoeffInFrame a⁻¹ * l.dsCoeffInFrame (g * a) =
        l.dsCoeffInFrame g := by
    have h_deg : (l.formalDegree : ℂ) ≠ 0 := ofReal_ne_zero.2 (formalDegree_pos h_gap).ne'
    have h_one : l.dsCoeffInFrame (1 : 𝔰.G₁) = 1 := by
      rw [dsCoeffInFrame, show frameEquiv (ε := ε) 1 = 1 from frameEquiv.map_one]
      exact dsCoeff_one
    have h_product := h_kernel.integral_inv_mul_translate g 1
    simp only [mul_one, h_one, div_mul_cancel₀ _ h_deg] at h_product
    rw [← mul_right_inj' h_deg, ← h_product, ← integral_const_mul]
    exact integral_congr_ae (.of_forall fun a ↦ mul_left_comm ..)
  funext y
  have h_reprod_integrand (s : 𝔰.besselGraph) :
      ∫ a : 𝔰.G₁, (l.formalDegree * l.dsCoeffInFrame a⁻¹) • besselIntegrand l rep x v (y * a) s =
        besselIntegrand l rep x v y s := by
    have h_eq (a : 𝔰.G₁) :
        (l.formalDegree * l.dsCoeffInFrame a⁻¹) • besselIntegrand l rep x v (y * a) s =
          (l.formalDegree * l.dsCoeffInFrame a⁻¹ *
            l.dsCoeffInFrame (x⁻¹ * (s.val.fst * y) * a)) •
            (wave (-simpleRootSum s.val.fst) • (besselValueRep rep s.val.snd⁻¹).val v) := by
      dsimp only [besselIntegrand]
      rw [smul_smul, ← mul_assoc s.val.fst y a, ← mul_assoc x⁻¹]
    simp_rw [h_eq]
    rw [integral_smul_const, h_reprod (x⁻¹ * (s.val.fst * y))]
    rfl
  -- The double integral converges, by the covering bound and the integrability of the kernel.
  have h_ker_cont : Continuous fun a : 𝔰.G₁ ↦ (l.formalDegree : ℂ) * l.dsCoeffInFrame a⁻¹ :=
    continuous_const.fun_mul (continuous_dsCoeffInFrame.comp continuous_inv)
  have h_int : Integrable (Function.uncurry fun (a : 𝔰.G₁) (s : 𝔰.besselGraph) ↦
      (l.formalDegree * l.dsCoeffInFrame a⁻¹) • besselIntegrand l rep x v (y * a) s)
      (volume.prod 𝔰.besselGraphMeasure) := by
    have h_joint_cont : Continuous (Function.uncurry fun (a : 𝔰.G₁) (s : 𝔰.besselGraph) ↦
        (l.formalDegree * l.dsCoeffInFrame a⁻¹) • besselIntegrand l rep x v (y * a) s) :=
      continuous_uncurry_smul_mul_left h_ker_cont (continuous_besselIntegrand x h_cont) y
    refine ⟨h_joint_cont.aestronglyMeasurable, (lintegral_prod_le _).trans_lt ?_⟩
    calc ∫⁻ a : 𝔰.G₁, ∫⁻ s : 𝔰.besselGraph,
          ‖(l.formalDegree * l.dsCoeffInFrame a⁻¹) • besselIntegrand l rep x v (y * a) s‖ₑ
          ∂𝔰.besselGraphMeasure
      _ ≤ ∫⁻ a : 𝔰.G₁, ‖l.formalDegree * l.dsCoeffInFrame a⁻¹‖ₑ *
          (.ofReal (16 ^ (9 * 𝔰.r ^ 2)) * besselBallVolume (ε := ε) x) := by
        simp_rw [eNorm_smul, lintegral_const_mul' _ _ eNorm_ne_top]
        exact lintegral_mono fun a ↦
          mul_le_mul' le_rfl (lintegral_enorm_besselIntegrand_le x hv_norm h_gap (y * a))
      _ < ∞ := by
        rw [lintegral_mul_const _ (show Measurable fun a : 𝔰.G₁ ↦
          ‖(l.formalDegree : ℂ) * l.dsCoeffInFrame a⁻¹‖ₑ from
            (continuous_eNorm.comp h_ker_cont).measurable)]
        exact mul_lt_top h_kernel.integrable.comp_inv.hasFiniteIntegral
          (mul_lt_top ofReal_lt_top (besselBallVolume_ne_top x).lt_top)
  simp only [besselAverage, convolve, ← integral_smul, integral_integral_swap h_int,
    h_reprod_integrand]

/-- For a unit vector `v`, the norm of `besselAverage l rep x v y` is at most the integral of
`|c_λ(x⁻¹ s y)|` over `s` in `R`, where `c_λ = l.dsCoeffInFrame`. -/
lemma enorm_besselAverage_le (hv_norm : ‖v‖ = 1) (y : 𝔰.G₁) :
    ‖besselAverage l rep x v y‖ₑ ≤
      ∫⁻ s : 𝔰.besselGraph, ‖l.dsCoeffInFrame (x⁻¹ * (s.val.fst * y))‖ₑ
        ∂𝔰.besselGraphMeasure := by
  simp_rw [← enorm_besselIntegrand (rep := rep) x hv_norm]
  exact eNorm_integral_le_lintegral_eNorm _

/-- Let `rep` be a continuous unitary representation of `H`, `v` a unit vector, and `l = 2λ` a
parameter with coefficient `c_λ = l.dsCoeffInFrame` and large gap. Then
`W = besselAverage l rep x v`, given by `W(y) = ∫_R c_λ(x⁻¹ s y) π(s)⁻¹ v ds` with `π` the unitary
representation of `R = 𝖴 H` in `besselIntegrand`, is integrable for `besselQuotMeasure`, the measure
on G₁ that computes integrals over 𝖴∖G₁. -/
lemma integrable_besselAverage (h_cont : Continuous rep) (hv_norm : ‖v‖ = 1)
    (h_gap : l.HasLargeGap excess) : Integrable (besselAverage l rep x v) besselQuotMeasure := by
  -- The upper bound of `‖W‖` unfolds to the integral of `|c_λ|` over G₁.
  have h_coeff_int : Integrable (l.dsCoeffInFrame : 𝔰.G₁ → ℂ) :=
    (integrable_const_mul_iff (ofReal_ne_zero.2 (formalDegree_pos h_gap).ne').isUnit _).1
      (isIdempotentKernel_dsCoeffInFrame h_gap).integrable
  refine ⟨(isBesselFunction_besselAverage x h_cont hv_norm
    h_gap).stronglyMeasurable.aestronglyMeasurable, ?_⟩
  calc _ ≤ ∫⁻ y : 𝔰.G₁, ∫⁻ s : 𝔰.besselGraph, ‖l.dsCoeffInFrame (x⁻¹ * (s.val.fst * y))‖ₑ
          ∂𝔰.besselGraphMeasure ∂besselQuotMeasure :=
      lintegral_mono (enorm_besselAverage_le x hv_norm)
    _ = ∫⁻ g : 𝔰.G₁, ‖l.dsCoeffInFrame g‖ₑ :=
      (lintegral_unfold_besselGraphMeasure (‖l.dsCoeffInFrame ·‖ₑ)
        (continuous_eNorm.comp continuous_dsCoeffInFrame).measurable).symm
    _ < ∞ := h_coeff_int.hasFiniteIntegral

/-- The norm is a period. Let `rep` be a continuous unitary representation of `H`, `v` a unit
vector, and `l = 2λ` a parameter with coefficient `c_λ = l.dsCoeffInFrame`, formal degree `deg` and
large gap. Let `W = besselAverage l rep x v`. Then `deg ‖W‖₂ ^ 2 = ⟪v, W(x)⟫`, the norm being that
of L²(𝖴∖G₁), computed by `besselQuotMeasure`. -/
lemma formalDegree_mul_integral_norm_sq_besselAverage (h_cont : Continuous rep) (hv_norm : ‖v‖ = 1)
    (h_gap : l.HasLargeGap excess) :
    ((l.formalDegree * ∫ y : 𝔰.G₁, ‖besselAverage l rep x v y‖ ^ 2 ∂besselQuotMeasure : ℝ) : ℂ) =
      ⟪v, besselAverage l rep x v x⟫_ℂ := by
  have : ContinuousMul 𝔰.G₁ := continuousMul_G₁
  have : SFinite 𝔰.besselGraphMeasure := sFinite_besselGraphMeasure
  -- Insert the integral for one factor of `⟪W y, W y⟫`, unfold, and use that `e_λ` reproduces `W`
  -- at the point `x`.
  set W : 𝔰.G₁ → EuclideanSpace ℂ I := besselAverage l rep x v
  have hW : IsBesselFunction rep W := isBesselFunction_besselAverage x h_cont hv_norm h_gap
  have h_kernel : IsIdempotentKernel fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g :=
    isIdempotentKernel_dsCoeffInFrame h_gap
  -- `Φ` is the integrand of `deg * ⟪W, W⟫` after one factor has been unfolded to G₁.
  let Φ (g : 𝔰.G₁) : ℂ := conj (l.formalDegree * l.dsCoeffInFrame (x⁻¹ * g)) * ⟪v, W g⟫_ℂ
  have hΦ_int : Integrable Φ := by
    obtain ⟨C, hC⟩ := hW.bounded
    refine (conjCLE.integrable_comp_iff.2 (h_kernel.integrable.comp_mul_left x⁻¹)).mul_bdd
      (c := ‖v‖ * C) hW.stronglyMeasurable.aestronglyMeasurable.const_inner (.of_forall fun g ↦ ?_)
    exact (norm_inner_le_norm v (W g)).trans (mul_le_mul_of_nonneg_left (hC g) (norm_nonneg v))
  have h_insert (y : 𝔰.G₁) : ∫ s : 𝔰.besselGraph, Φ (s.val.fst * y) ∂𝔰.besselGraphMeasure =
      l.formalDegree * (‖W y‖ ^ 2 : ℂ) := by
    have h_point (s : 𝔰.besselGraph) :
        Φ (s.val.fst * y) = l.formalDegree * conj ⟪W y, besselIntegrand l rep x v y s⟫_ℂ := by
      -- Move `π(s)` to the other side of the inner product, as `π(s)⁻¹ = π(s)*`.
      have h_wave_conj : conj (wave (-simpleRootSum s.val.fst)) =
          wave (simpleRootSum s.val.fst) := by
        rw [wave, wave, ← Complex.exp_conj]
        congr 1
        simp only [map_sub, map_neg, RingHomCompTriple.comp_apply, RingHom.id_apply]
        ring
      have h_adj : ⟪v, (besselValueRep rep s.val.snd).val (W y)⟫_ℂ =
          conj ⟪W y, (besselValueRep rep s.val.snd⁻¹).val v⟫_ℂ := by
        rw [inner_conj_symm, besselValueRep_inv_val]
        exact (ContinuousLinearMap.adjoint_inner_left
          (besselValueRep rep s.val.snd).val (W y) v).symm
      dsimp only [Φ, W, besselIntegrand]
      rw [besselAverage_mul x h_cont hv_norm h_gap s y, inner_smul_right, inner_smul_right,
        inner_smul_right, map_mul, map_mul, map_mul, Complex.conj_ofReal, h_wave_conj, h_adj]
      ring
    simp_rw [h_point, integral_const_mul, integral_conj,
      integral_inner (integrable_besselIntegrand x h_cont hv_norm h_gap y), inner_conj_symm]
    exact congrArg _ (inner_self_eq_norm_sq_to_K (W y))
  calc _ = ∫ y : 𝔰.G₁, ∫ s : 𝔰.besselGraph, Φ (s.val.fst * y)
          ∂𝔰.besselGraphMeasure ∂besselQuotMeasure := by
        simp_rw [h_insert, integral_const_mul, ← Complex.ofReal_pow, integral_complex_ofReal,
          Complex.ofReal_mul]
    _ = ∫ g : 𝔰.G₁, Φ g := by
      have h_unfold := measurePreserving_unfold_besselGraphMeasure (𝔰 := 𝔰)
      rw [← h_unfold.map_eq] at hΦ_int ⊢
      rw [integral_map h_unfold.aemeasurable hΦ_int.aestronglyMeasurable]
      exact (integral_prod _ (hΦ_int.comp_measurable h_unfold.measurable)).symm
    _ = ∫ a : 𝔰.G₁, ⟪v, (l.formalDegree * l.dsCoeffInFrame a⁻¹) • W (x * a)⟫_ℂ := by
      rw [← integral_mul_left_eq_self _ x]
      simp only [Φ, inv_mul_cancel_left, inner_smul_right, ← h_kernel.apply_inv]
    _ = ⟪v, convolve W (fun g : 𝔰.G₁ ↦ l.formalDegree * l.dsCoeffInFrame g) x⟫_ℂ :=
      integral_inner (hW.integrable_smul h_kernel.integrable.comp_inv x) v
    _ = ⟪v, W x⟫_ℂ := by rw [convolve_besselAverage x h_cont hv_norm h_gap]

/-- Let `rep` be a continuous unitary representation of `H` on `ℂ^I`, `v` a vector of `ℂ^I` such
that `⟪v, rep k v⟫` is the coefficient of the parameter `u` at each `k` in `H`, and `l = 2λ` a
parameter with coefficient `c_λ = l.dsCoeffInFrame` and large gap. Let `π` be the representation of
`R = 𝖴 H` that is `rep` on `H` and the character `g ↦ exp (σ - conj σ)`, `σ = simpleRootSum g`, on
`𝖴`. Let `W = besselAverage l rep x v`. Suppose that `besselBallVolume x`, the volume of
`{‖x⁻¹ s x - 1‖ ≤ 1}` in `R`, is at most `P ≥ 0` times the modulus of the period
`∫_R c_λ(x⁻¹ s x) ⟪v, π(s)⁻¹ v⟫ ds`. Then it is at most `P` times the formal degree of `l` times
`‖W‖₂ ^ 2`, the norm being that of L²(𝖴∖G₁). -/
lemma besselBallVolume_le_of_period (h_cont : Continuous rep) (h_gap : l.HasLargeGap excess)
    {u : HCParam (1 : 𝔰.κ → ℤˣ)} {P : ℝ} (hP : 0 ≤ P)
    (hv : ∀ k : U (1 : Matrix 𝔰.κ 𝔰.κ ℂ), ⟪v, (besselValueRep rep k).val v⟫_ℂ = u.dsCoeff k)
    (h_period : 𝔰.besselGraphMeasure.real
        {s : 𝔰.besselGraph | ‖(subOnePair (besselPairHom (ε := ε) x) s).fst‖ ≤ 1} ≤
      P * ‖∫ s : 𝔰.besselGraph, l.laplaceIntegrand u (besselPairHom x)
        (fun s' : 𝔰.besselGraph ↦ simpleRootSum s'.val.fst - conj (simpleRootSum s'.val.fst)) s
        ∂𝔰.besselGraphMeasure‖) :
    besselBallVolume (ε := ε) x ≤ .ofReal P *
      (.ofReal l.formalDegree *
        ∫⁻ y : 𝔰.G₁, ‖besselAverage l rep x v y‖ₑ ^ 2 ∂besselQuotMeasure) := by
  have h_sq : ‖v‖ ^ 2 = 1 := by
    have h1 := hv 1
    rw [(besselValueRep rep).map_one, OneMemClass.coe_one, one_apply_eq_self,
      inner_self_eq_norm_sq_to_K] at h1
    have h2 : (‖v‖ : ℂ) ^ 2 = 1 := h1.trans dsCoeff_one
    exact_mod_cast h2
  have hv_norm : ‖v‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg v) two_ne_zero).1 h_sq
  have h_deg : 0 ≤ l.formalDegree := (formalDegree_pos h_gap).le
  -- The period is `⟪v, W x⟫`, as `conj c_u(h) = conj ⟪v, π(h) v⟫ = ⟪v, π(h)⁻¹ v⟫`.
  have h_inner : ∫ s : 𝔰.besselGraph, l.laplaceIntegrand u (besselPairHom x)
      (fun s' : 𝔰.besselGraph ↦ simpleRootSum s'.val.fst - conj (simpleRootSum s'.val.fst)) s
      ∂𝔰.besselGraphMeasure = ⟪v, besselAverage l rep x v x⟫_ℂ := by
    rw [besselAverage, ← integral_inner (integrable_besselIntegrand x h_cont hv_norm h_gap x)]
    refine integral_congr_ae (.of_forall fun s ↦ ?_)
    have h_fst : (besselPairHom (ε := ε) x s).fst = frameEquiv (x⁻¹ * (s.val.fst * x)) := by
      change frameEquiv (x⁻¹ * s.val.fst * x) = _
      rw [mul_assoc]
    have h_snd : u.dsCoeff (besselPairHom (ε := ε) x s).snd =
        ⟪v, (besselValueRep rep s.val.snd).val v⟫_ℂ := (hv s.val.snd).symm
    have h_adj : conj ⟪v, (besselValueRep rep s.val.snd).val v⟫_ℂ =
        ⟪v, (besselValueRep rep s.val.snd⁻¹).val v⟫_ℂ := by
      rw [inner_conj_symm, besselValueRep_inv_val]
      exact (ContinuousLinearMap.adjoint_inner_right
        (besselValueRep rep s.val.snd).val v v).symm
    have h_exp : cexp (-(simpleRootSum s.val.fst - conj (simpleRootSum s.val.fst))) =
        wave (-simpleRootSum s.val.fst) := by
      rw [wave]
      congr 1
      rw [map_neg]
      ring
    dsimp only [laplaceIntegrand, besselIntegrand]
    rw [h_fst, ← dsCoeffInFrame, h_snd, h_adj, h_exp, inner_smul_right, inner_smul_right]
    ring
  have h_nonneg :
      0 ≤ l.formalDegree * ∫ y : 𝔰.G₁, ‖besselAverage l rep x v y‖ ^ 2 ∂besselQuotMeasure :=
    mul_nonneg h_deg (integral_nonneg fun y ↦ sq_nonneg _)
  rw [h_inner, ← formalDegree_mul_integral_norm_sq_besselAverage x h_cont hv_norm h_gap,
    Complex.norm_of_nonneg h_nonneg] at h_period
  -- The set in `h_period` is the ball of `besselBallVolume`, by the definition of `subOnePair`.
  rwa [lintegral_enorm_sq (integrable_besselAverage x h_cont hv_norm h_gap)
      (isBesselFunction_besselAverage x h_cont hv_norm h_gap).memLp_top,
    ← ENNReal.ofReal_mul h_deg, ← ENNReal.ofReal_mul hP,
    le_ofReal_iff_toReal_le (besselBallVolume_ne_top x) (mul_nonneg hP h_nonneg)]

end New.DiscreteSeries

end
