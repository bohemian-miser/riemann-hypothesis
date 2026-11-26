module

public import Aesop.BuiltinRules
public import Mathlib.RingTheory.Invariant.Defs
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.RingTheory.Invariant.Basic
import TauCeti.RingTheory.MvPolynomial.Homogeneous
import TauCeti.RingTheory.NoetherNormalization
public import Lib.General.Geometry.ProjectiveSpace
public import Lib.General.Geometry.EtaleCharts
import Lib.General.Algebra.MultivariatePolynomials
import Lib.General.Geometry.PointsOfProperSchemes
import Lib.PadicComparison.Descent.TestCategory

/-!
# Projective Noether normalisation and homogeneous coordinates of embedded points

Let k be a field. For a tuple `g : ι → L`, `New.Variety.CutsOutLocus.IsHomogeneousSolution k g w`
says that every homogeneous polynomial over k that vanishes at g also vanishes at w. The file proves
projective Noether normalisation by linear forms in characteristic zero and constructs its Galois
closure.

## Main definitions and results

* `New.Variety.CutsOutLocus.IsNoetherNormalization Λ g`: the linear forms `Λ₀, …, Λ_d` are a Noether
  normalisation of the cone, that is, their values at `g` are independent and the cone is integral
  over them.
* `New.Variety.CutsOutLocus.exists_isNoetherNormalization`: such forms exist for a non-zero finite
  tuple `g` over a field `k` of characteristic zero.
* `New.Variety.CutsOutLocus.IsNoetherNormalization.GaloisClosure`,
  `New.Variety.CutsOutLocus.IsNoetherNormalization.nonempty_galoisClosure`: the Galois closure of
  the normalisation, a finite algebra `B` over `k[X₀, …, X_d]` with points `b σ` of the cone,
  indexed by a finite group.
* `New.Variety.IsCoordsWithUnit.exists_universal_chart`,
  `New.Variety.IsCoordsWithUnit.exists_mem_open_of_isUnit`: a point ξ over a field F with
  coordinates g spreads out and specialises to the vectors w with w i (resp. aeval w b) a unit that
  satisfy the homogeneous relations of g.
* `New.Variety.IsCoordsWithUnit.exists_app_eq_algebraMap_of_isHomogeneousSolution`: over an
  algebraically closed k, a global function takes one constant value on all such specialisations.

Notions from other files:
* `New.LineBundle.IsHomogeneousCoords`: v is a vector of homogeneous coordinates of the point t for
  L: t lands in U_j exactly when v_j is a unit, and then g_jk(t) = v_k/v_j.
* `New.Variety.IsOpenSubfunctor`: V is an open subfunctor of X: each x ∈ X(A) has an ideal I of A
  such that, for φ: A → B, φ(x) ∈ V(B) iff φ(I)B = B.

## Relation to the literature

Known; see `Lib.Cohomology.PointClass.LinearIndependence` for sources.
-/

@[expose] public section

/-!
## Noether normalisation of a cone by linear forms

Noether normalisation is stated for coordinate vectors instead of varieties. A tuple `g : ι → L`
stands for the cone cut out by the homogeneous polynomials over `k` that vanish at `g`.
-/

section NoetherNormalization

open Fin MvPolynomial Finset Function Finite IsScalarTower FaithfulSMul Algebra Ideal RingHom

namespace New.Variety.CutsOutLocus

variable {k L ι A B C : Type} [Field k] [Field L] [Algebra k L] [CommRing A] [Algebra k A]
  {u : A} [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
  {g : ι → B} {v : ι → A} {d : ℕ} (Λ : Fin (d + 1) → homogeneousSubmodule ι k 1)
  {F : MvPolynomial ι k} (φ : A →ₐ[k] C) (ψ : A →ₐ[k] L)

/-! ### The cone of a coordinate vector -/

variable (k g v) in
/-- The point `v` lies on the cone of `g`: every homogeneous polynomial over `k` that vanishes at
`g` vanishes at `v`. The two tuples may have entries in different `k`-algebras. -/
def IsHomogeneousSolution : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃F : MvPolynomial ι k⦄, F.IsHomogeneous n → F.aeval g = 0 → F.aeval v = 0

/-- The tuple of values of the polynomials `Λ j` at `v`. -/
noncomputable abbrev evalForms (v : ι → A) (j : Fin (d + 1)) : A := ((Λ j).val.aeval v : A)

/-- If `χ` kills the kernel of `φ` and `φ ∘ v` lies on the cone of `g`, then so does `χ ∘ v`. -/
lemma IsHomogeneousSolution.of_ker {D : Type} [CommRing D] [Algebra k D] (χ : A →ₐ[k] D)
    (h_ker : ∀ r : A, φ r = 0 → χ r = 0) (h_sol : IsHomogeneousSolution k g (φ ∘ v)) :
    IsHomogeneousSolution k g (χ ∘ v) := fun _ F hF h_g ↦
  -- `F (χ ∘ v) = χ (F v)`, and `φ (F v) = F (φ ∘ v) = 0`
  (comp_aeval_apply v χ F).symm.trans (h_ker _ ((comp_aeval_apply v φ F).trans (h_sol hF h_g)))

lemma IsHomogeneousSolution.map : IsHomogeneousSolution k g v → IsHomogeneousSolution k g (φ ∘ v) :=
  of_ker 1 φ (by simp)

lemma IsHomogeneousSolution.smul (u : C) (h : IsHomogeneousSolution k g v) :
    IsHomogeneousSolution k g (u • φ ∘ v) := by
  intro n F hF h_g
  have h_map : aeval (φ ∘ v) F = 0 := h.map φ hF h_g
  rw [hF.aeval_smul_of_algebra, h_map, smul_zero]

@[simp]
lemma evalForms_map (v : ι → A) : evalForms Λ (φ ∘ v) = φ ∘ evalForms Λ v := by
  simp [comp_aeval_apply, comp_def]

@[simp]
lemma evalForms_smul : evalForms Λ (u • v) = u • evalForms Λ v := by
  simp [funext_iff, ((Λ _).prop).aeval_smul_of_algebra]

/-- If `t` is transcendental over the ring `B` of the entries of `g`, every polynomial that
vanishes at `t • g`, homogeneous or not, vanishes at each point `v` of the cone of `g`. -/
lemma IsHomogeneousSolution.aeval_eq_zero_of_transcendental [Algebra B L] [IsScalarTower k B L]
    {t : L} (ht : Transcendental B t) (h_sol : IsHomogeneousSolution k g v)
    (h_zero : aeval (t • algebraMap B L ∘ g) F = 0) :
    aeval v F = 0 := by
  -- Split `F` into homogeneous components `F_n`. The values `F_n(g)` are the coefficients of a
  -- polynomial over `B` that vanishes at `t`, so they are zero.
  let P : Polynomial B :=
    ∑ n ∈ range (F.totalDegree + 1), .monomial n (aeval g (homogeneousComponent n F))
  rw [← F.sum_homogeneousComponent, map_sum] at h_zero ⊢
  -- `P (t)` is the sum in `h_zero`, by homogeneity of the `F_n`
  have h_sum : P.aeval t = ∑ n ∈ range (F.totalDegree + 1),
      aeval (t • algebraMap B L ∘ g) (homogeneousComponent n F) := by
    simp [P, Polynomial.aeval_monomial, mul_comm, aeval_algebraMap_apply,
      (homogeneousComponent_mem _ F).aeval_smul_of_algebra]
  have hP : P = 0 := transcendental_iff.mp ht P (h_sum.trans h_zero)
  refine sum_eq_zero fun n hn ↦ h_sol (homogeneousComponent_mem n F) ?_
  -- the value `F_n(g)` is the `n`-th coefficient of `P = 0`
  simpa [P, Polynomial.coeff_monomial, Finsupp.single_apply, hn] using
    congrArg (fun p : Polynomial B ↦ p.coeff n) hP

lemma IsHomogeneousSolution.refl : IsHomogeneousSolution k v v := by tauto

/-- An element of a field `L` that lies in every valuation ring containing the image of `f` is
integral over that image. -/
@[stacks 090P "part (1), for the integral closure of the image of a ring map"]
lemma isIntegralElem_of_valuationSubring {f : A →+* L} {x : L}
    (h : ∀ V : ValuationSubring L, (∀ a : A, f a ∈ V) → x ∈ V) :
    f.IsIntegralElem x := by
  -- The integral closure of `A` in `L` is the intersection of the valuation rings that contain it.
  let algebraL : Algebra A L := f.toAlgebra
  refine (integralClosure A L).toSubring.eq_iInf_of_isIntegrallyClosedIn.ge ?_
  simpa using fun V hV ↦ h V fun a ↦ hV isIntegral_algebraMap

/-! ### Noether normalisation -/

/-- Λ is a Noether normalisation of g: the Λ_0, …, Λ_d are linear forms, the values Λ_j(g) have no
non-zero homogeneous relation, and every field-valued point v of the cone of g is integral over
any image of a `k`-algebra that contains the values Λ_j(v). -/
def IsNoetherNormalization (g : ι → L) : Prop :=
  -- the values of the forms `Λ j` at `g` satisfy no non-zero homogeneous relation over `k`
  IsHomogeneousSolution k (evalForms Λ g) (X (R := k)) ∧
  -- a solution `v` of the homogeneous equations of `g` is integral over every ring `R` whose
  -- image contains the values of `Λ` at `v`
  ∀ {K R : Type} [Field K] [Algebra k K] [CommRing R] [Algebra k R] (φ : R →ₐ[k] K)
      (p : Fin (d + 1) → R) (v : ι → K),
    IsHomogeneousSolution k g v → evalForms Λ v = φ ∘ p → ∀ i : ι,
    φ.IsIntegralElem (v i)

/-- Let `φ : A → C` be integral and `ψ : A → L` a map to an algebraically closed field whose
kernel contains that of `φ`. Then `ψ = χ ∘ φ` for some map `χ : C → L` of `k`-algebras. -/
lemma exists_algHom_comp_eq_of_integral [IsAlgClosed L] (hφ_int : φ.IsIntegral)
    (h_ker : ker φ ≤ ker ψ) :
    ∃ χ : C →ₐ[k] L, χ.comp φ = ψ := by
  -- Take a prime `q` of `C` over the kernel of `ψ`. Then `C ⧸ q` is an algebraic extension of the
  -- domain `A ⧸ ker ψ`, whose embedding in `L` extends.
  algebraize [φ.toRingHom, (kerLiftAlg ψ).toRingHom]
  have h_prime : (ker ψ).IsPrime := ker_isPrime ψ
  obtain ⟨q, -, hq_prime, hq⟩ :
      ∃ q ≥ (⊥ : Ideal C), q.IsPrime ∧ q.comap (algebraMap A C) = ker ψ :=
    exists_ideal_over_prime_of_isIntegral (ker ψ) (⊥ : Ideal C) h_ker
  have : q.LiesOver (ker ψ) := ⟨hq.symm⟩
  have h_alg : Algebra.IsAlgebraic (A ⧸ ker ψ) (C ⧸ q) :=
    (Algebra.IsIntegral.tower_top A).isAlgebraic
  have : Module.IsTorsionFree (A ⧸ ker ψ) L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (kerLiftAlg_injective ψ)
  have : Module.IsTorsionFree (A ⧸ ker ψ) (C ⧸ q) :=
    FaithfulSMul.to_isTorsionFree (A ⧸ ker ψ) (C ⧸ q)
  let χ : C ⧸ q →ₐ[A ⧸ ker ψ] L := IsAlgClosed.lift
  exact ⟨(χ.restrictScalars k).comp (toAlgHom k C _), AlgHom.ext fun a ↦ χ.commutes ⟦a⟧⟩

variable {Λ} {g : ι → L}

open IsIntegralClosure FiniteGaloisIntermediateField in
/-- Finitely many elements of an algebraically closed field, integral over a noetherian normal
domain `A` of characteristic zero, lie in a finite `A`-algebra `B` whose ring of invariants is
`A`. -/
lemma exists_galois_hull [Finite ι]
    [IsDomain A] [IsNoetherianRing A] [CharZero A] [IsIntegrallyClosed A]
    [IsAlgClosed L] [Algebra A L] [FaithfulSMul A L] (hg : ∀ i : ι, IsIntegral A (g i)) :
    ∃ B : CommAlgCat.{0} A, ∃ _ : Fintype Gal(B/A), ∃ j : B →ₐ[A] L, ∃ x : ι → B,
      Algebra.IsInvariant A B Gal(B/A) ∧ (algebraMap A B).Finite ∧ Injective j ∧ j ∘ x = g := by
  -- `B` is the integral closure of `A` in a finite Galois extension `N` of `Frac A` in `L` that
  -- contains the `g i`.
  let K : Type := FractionRing A
  let algebraKL : Algebra K L := FractionRing.liftAlgebra A L
  let g' (i : ι) : algebraicClosure K L := ⟨g i, (hg i).tower_top⟩
  let N : IntermediateField K (algebraicClosure K L) :=
    (FiniteGaloisIntermediateField.adjoin K (.range g')).toIntermediateField
  let B : Subalgebra A N := integralClosure A N
  have h_frac : IsFractionRing B N := isFractionRing_of_finite_extension A K N B
  let x (i : ι) : B :=
    ⟨⟨g' i, subset_adjoin K _ ⟨i, rfl⟩⟩, .of_map (algebraMap_injective N L) (hg i)⟩
  let j : B →ₐ[A] L := ⟨algebraMap B L, fun _ ↦ rfl⟩
  exact ⟨.of A B, .ofEquiv _ (galRestrict A K N B).toEquiv, j, x, isInvariant_of_isGalois' A K N B,
    finite_algebraMap.mpr (finite A K N B), algebraMap_injective B L, rfl⟩

/-- Evaluation at `X • g` in `RatFunc L`; its kernel cuts out the homogeneous coordinate ring of
the cone of `g`. -/
private noncomputable abbrev coneEval (k : Type) [Field k] [Algebra k L] (g : ι → L) :
    MvPolynomial ι k →ₐ[k] RatFunc L :=
  aeval ((RatFunc.X : RatFunc L) • algebraMap L (RatFunc L) ∘ g)

/-- If `a : Q` is integral over `aeval y : k[Fin d'] → Q` and a `k`-algebra map `ev : Q → K`
intertwines `aeval y` with `φ ∘ aeval p`, then `ev a` is integral over `φ`. -/
private lemma isIntegralElem_of_comp_aeval_eq {Q K R : Type} [CommRing Q] [Algebra k Q]
    [CommRing K] [Algebra k K] [CommRing R] [Algebra k R] {d' : ℕ} {y : Fin d' → Q}
    {a : Q} (ha : (aeval (R := k) y).toRingHom.IsIntegralElem a) (φ : R →ₐ[k] K)
    (p : Fin d' → R) (ev : Q →ₐ[k] K) (hev : ev.comp (aeval y) = φ.comp (aeval p)) :
    φ.IsIntegralElem (ev a) := by
  obtain ⟨q, hq_monic, hq_eval⟩ := ha
  refine ⟨q.map (aeval p).toRingHom, hq_monic.map _, ?_⟩
  have hev' : φ.toRingHom.comp (aeval p).toRingHom = ev.toRingHom.comp (aeval y).toRingHom :=
    congrArg AlgHom.toRingHom hev.symm
  rw [Polynomial.eval₂_map, hev']
  simpa [Polynomial.hom_eval₂] using congrArg ev.toRingHom hq_eval

/-- For a non-zero tuple `g : ι → L`, the homogeneous coordinate ring `k[ι] / ker (coneEval k g)`
of the cone of `g` cannot be finite over `k[Fin 0]`: since `RatFunc.X` is transcendental over `L`,
some coordinate `X * g i₀` is not integral over `L`. -/
private lemma dim_ne_zero_of_finite_cone {d' : ℕ} (hg : g ≠ 0)
    (y : Fin d' → MvPolynomial ι k ⧸ ker (coneEval k g))
    (hy_fin : (aeval (R := k) y).toRingHom.Finite) : d' ≠ 0 := by
  rintro rfl
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hg
  have hcomp : (kerLiftAlg (coneEval k g)).comp (aeval y) =
      (toAlgHom k L (RatFunc L)).comp (aeval Fin.elim0) := algHom_ext fun i ↦ i.elim0
  have hker_x : kerLiftAlg (coneEval k g) (Quotient.mkₐ k (ker (coneEval k g)) (X i₀)) =
      RatFunc.X * algebraMap L (RatFunc L) (g i₀) := by
    rw [Ideal.Quotient.mkₐ_eq_mk, kerLiftAlg_mk]
    simp [coneEval]
  have h_int : IsIntegral L (RatFunc.X * algebraMap L (RatFunc L) (g i₀)) := by
    rw [← hker_x]
    exact isIntegralElem_of_comp_aeval_eq
      (hy_fin.to_isIntegral (Quotient.mkₐ k (ker (coneEval k g)) (X i₀)))
      (toAlgHom k L (RatFunc L)) Fin.elim0 (kerLiftAlg (coneEval k g)) hcomp
  have hX : IsIntegral L (RatFunc.X : RatFunc L) := by
    have hmul : IsIntegral L (RatFunc.X * algebraMap L (RatFunc L) (g i₀) *
        algebraMap L (RatFunc L) (g i₀)⁻¹) := h_int.mul isIntegral_algebraMap
    rwa [mul_assoc, ← map_mul, mul_inv_cancel₀ hi₀, map_one, mul_one] at hmul
  exact RatFunc.transcendental_X hX.isAlgebraic

/-- If the classes of linear forms `Λ` in the homogeneous coordinate ring
`k[ι] / ker (coneEval k g)` of the cone of `g` are algebraically independent over `k`, then the
values `Λ j (g)` satisfy no non-zero homogeneous polynomial relation over `k`. -/
private lemma isHomogeneousSolution_evalForms_of_algebraicIndependent
    (hy_ind : AlgebraicIndependent k fun l : Fin (d + 1) ↦
      Quotient.mkₐ k (ker (coneEval k g)) (Λ l).val) :
    IsHomogeneousSolution k (evalForms Λ g) (X (R := k)) := by
  intro m F hF h_rel
  let F' : MvPolynomial ι k := aeval (fun l ↦ (Λ l).val) F
  have hF' : F'.IsHomogeneous m := by simpa using hF.aeval _ fun l ↦ (Λ l).prop
  have hFg : aeval g F' = 0 := (comp_aeval_apply _ (aeval g) F).trans h_rel
  have hΨF' : F' ∈ ker (coneEval k g) := by
    rw [RingHom.mem_ker]
    dsimp only [coneEval]
    rw [hF'.aeval_smul_of_algebra, aeval_algebraMap_apply, hFg, map_zero, smul_zero]
  have hyF : aeval (fun l ↦ Quotient.mkₐ k (ker (coneEval k g)) (Λ l).val) F = 0 := by
    rw [← comp_aeval_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hΨF'
  simp [algebraicIndependent_iff.mp hy_ind F hyF]

/-- Noether normalisation. Let `g` be a non-zero tuple, indexed by a finite type `ι`, in a field `L`
over a field `k` of characteristic zero. Then there are linear forms `Λ₀, …, Λ_d` over `k` with
`Λ₀(g) ≠ 0` that form a Noether normalisation of `u • g` for every unit `u` of `L`. This means the
values `Λ_j(u • g)` satisfy no non-zero homogeneous polynomial relation over `k`, and every
field-valued point `v` on the cone of `u • g` is integral over any image of a `k`-algebra that
contains the values `Λ_j(v)`. -/
lemma exists_isNoetherNormalization [CharZero k] [Finite ι] (hg : g ≠ 0) :
    ∃ (d : ℕ) (Λ : Fin (d + 1) → homogeneousSubmodule ι k 1),
      evalForms Λ g 0 ≠ 0 ∧ ∀ u : Lˣ, IsNoetherNormalization (k := k) (d := d) Λ (u • g) := by
  -- Apply linear Noether normalisation (`TauCeti.exists_linear_normalization_of_finite`) to the
  -- homogeneous coordinate ring `Q = k[ι] / ker Ψ` of the cone of `g`, cut out by `X • g` in
  -- `RatFunc L`.
  let Ψ : MvPolynomial ι k →ₐ[k] RatFunc L := coneEval k g
  have hΨ_prime : (ker Ψ).IsPrime := ker_isPrime Ψ
  let Q : Type := MvPolynomial ι k ⧸ ker Ψ
  cases nonempty_fintype ι
  let x : ι → Q := fun i ↦ Quotient.mkₐ k (ker Ψ) (X i)
  have haeval : aeval (R := k) x = Quotient.mkₐ k (ker Ψ) := algHom_ext fun i ↦ aeval_X x i
  have hx_surj : Surjective (aeval (R := k) x) := by
    rw [haeval]
    exact Quotient.mkₐ_surjective k (ker Ψ)
  obtain ⟨d', -, C, hy_ind, hy_fin, -⟩ :=
    TauCeti.exists_linear_normalization_of_finite x (.of_surjective _ hx_surj)
  let y : Fin d' → Q := fun l ↦ ∑ j, C l j • x j
  -- The dimension `d'` is positive: since `g ≠ 0`, `Q` cannot be finite over `k[Fin 0]`.
  have hd' : d' ≠ 0 := dim_ne_zero_of_finite_cone hg y hy_fin
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd'
  let Λ : Fin (d + 1) → homogeneousSubmodule ι k 1 := fun l ↦
    ⟨∑ j, C l j • X j, sum_mem fun j _ ↦ Submodule.smul_mem _ _ (isHomogeneous_X k _)⟩
  have hy_eq : y = fun l ↦ Quotient.mkₐ k (ker Ψ) (Λ l).val := funext fun l ↦ by
    simp only [y, Λ, x, map_sum, map_smul]
  -- Algebraic independence of `y` in `Q` means the `Λ l (g)` satisfy no homogeneous relation.
  have hy_ind' : AlgebraicIndependent k fun l ↦ Quotient.mkₐ k (ker Ψ) (Λ l).val := by
    rw [← hy_eq]
    exact hy_ind
  have h_ind : IsHomogeneousSolution k (evalForms Λ g) (X (R := k)) :=
    isHomogeneousSolution_evalForms_of_algebraicIndependent hy_ind'
  -- no relation: in particular `X 0` is none, so `Λ 0` does not vanish at `g`
  have h_ne : evalForms Λ g 0 ≠ 0 := by simpa using h_ind (isHomogeneous_X k 0)
  refine ⟨d, Λ, h_ne, fun u ↦ ⟨fun m F hF h_rel ↦ h_ind hF ?_, fun φ p v hv h_val i ↦ ?_⟩⟩
  · -- no relation at `u • g` either: it would be one at `g`, up to a power of `u`
    simpa [u.smul_def, hF.aeval_smul_of_algebra] using h_rel
  · -- a point of the cone of `u • g` lies on the cone of `g`, so evaluation at `v` factors
    -- through `Q`, carrying integrality over `k[y]` to `φ`
    have hv_g : IsHomogeneousSolution k g v := fun n P hP hPg ↦
      hv hP (by simp [u.smul_def, hP.aeval_smul_of_algebra, hPg])
    have h_ker (P : MvPolynomial ι k) (hP : P ∈ ker Ψ) : aeval v P = 0 :=
      hv_g.aeval_eq_zero_of_transcendental RatFunc.transcendental_X hP
    let ev : Q →ₐ[k] _ := Quotient.liftₐ (ker Ψ) (aeval v) h_ker
    have hev_comp : ev.comp (aeval y) = φ.comp (aeval p) := algHom_ext fun l ↦ by
      rw [AlgHom.comp_apply, aeval_X, hy_eq, AlgHom.comp_apply, aeval_X]
      exact congrFun h_val l
    have hev_x : ev (x i) = v i := aeval_X v i
    rw [← hev_x]
    exact isIntegralElem_of_comp_aeval_eq (hy_fin.to_isIntegral (x i)) φ p ev hev_comp

/-- Let `A` be the ring of invariants of the finite group of `A`-automorphisms of `B`. Two maps
of `k`-algebras from `B` to a field (`k` of characteristic zero) that agree on `A` differ by such an
automorphism. -/
lemma exists_algEquiv_of_comp_eq [CharZero k] [Algebra A B] [IsScalarTower k A B] [Fintype Gal(B/A)]
    (hinv : Algebra.IsInvariant A B Gal(B/A)) {χ ψ : B →ₐ[k] L}
    (h_agree : χ.comp (toAlgHom k A B) = ψ.comp (toAlgHom k A B)) :
    ∃ τ : Gal(B/A), ∀ a : B, ψ a = χ (τ a) := by
  -- Two ring maps from `B` to the field `L` that agree on the invariant subring `A` have conjugate
  -- kernels above the same prime of `A`, hence differ by an element `τ` of the finite group
  -- `Gal(B/A)` (`TauCeti.Algebra.IsInvariant.exists_comp_eq_of_comp_algebraMap_eq`).
  -- Register `hinv` as an instance and pass the agreement on `A` as a `RingHom` equality.
  have h_inv : Algebra.IsInvariant A B Gal(B/A) := hinv
  have h_ring : χ.toRingHom.comp (algebraMap A B) = ψ.toRingHom.comp (algebraMap A B) :=
    congrArg AlgHom.toRingHom h_agree
  obtain ⟨τ, hτ⟩ : ∃ τ : Gal(B/A),
      χ.toRingHom.comp (MulSemiringAction.toRingHom Gal(B/A) B τ) = ψ.toRingHom :=
    TauCeti.Algebra.IsInvariant.exists_comp_eq_of_comp_algebraMap_eq
      A Gal(B/A) χ.toRingHom ψ.toRingHom h_ring
  exact ⟨τ, fun a ↦ (RingHom.congr_fun hτ a).symm⟩

/-- Let `t` be transcendental over `L`, `j : B → Ω` a map of `k`-algebras with zero kernel, and `b`
a tuple over `B` with `j ∘ b = t • w` for a tuple `w` of elements of `Ω` integral over `L`. Every
polynomial relation of `b` holds for `u • φ ∘ b`, for every map `φ` of `k`-algebras from `B` to a
field `K` and every `u`: the relation splits into homogeneous relations of `w`, which `b`
satisfies. -/
private lemma ker_aeval_le_ker_aeval_smul_of_transcendental {κ B K Ω : Type} [CommRing B]
    [Algebra k B] [Field K] [Algebra k K] [Field Ω] [Algebra L Ω] [Algebra k Ω]
    [IsScalarTower k L Ω] {t : Ω} (ht : Transcendental L t) (j : B →ₐ[k] Ω)
    (hj_ker : ∀ r : B, j r = 0 → r = 0) (b : κ → B) (w : κ → integralClosure L Ω)
    (hw : t • toAlgHom k (integralClosure L Ω) Ω ∘ w = j ∘ b) (φ : B →ₐ[k] K) (u : K) :
    ker (aeval (R := k) b) ≤ ker (aeval (R := k) (u • φ ∘ b)) := by
  have h_tw : IsHomogeneousSolution k w (t • toAlgHom k (integralClosure L Ω) Ω ∘ w) :=
    .smul _ t .refl
  rw [hw] at h_tw
  have hwb : IsHomogeneousSolution k w b :=
    .of_ker j (AlgHom.id k B) (fun r hr ↦ by rw [hj_ker r hr, map_zero]) h_tw
  refine fun F hF ↦ (hwb.smul φ u).aeval_eq_zero_of_transcendental ht.integralClosure ?_
  change aeval (t • toAlgHom k (integralClosure L Ω) Ω ∘ w) F = 0
  rw [hw]
  exact (comp_aeval_apply b j F).symm.trans (by rw [RingHom.mem_ker.mp hF, map_zero])

/-- Let `f : k[X₀, …, X_d] → B` be finite and `b` a family of tuples over `B` such that `Λ` takes
the tuple `b σ₀` to `f ∘ X`. Then `aeval b` is integral: composed with the substitution of the
forms `Λ` in the variables `(σ₀, i)`, it is `f`. -/
private lemma isIntegral_aeval_of_evalForms_eq {G B : Type} [CommRing B] [Algebra k B]
    (f : MvPolynomial (Fin (d + 1)) k →ₐ[k] B) (hf_fin : f.toRingHom.Finite) (b : G → ι → B)
    (σ₀ : G) (hΛb : evalForms Λ (b σ₀) = f ∘ X) :
    (aeval (R := k) ↿b).IsIntegral := by
  let θ : MvPolynomial (Fin (d + 1)) k →ₐ[k] MvPolynomial (G × ι) k :=
    aeval fun l ↦ rename (Prod.mk σ₀) (Λ l).val
  have hfactor : (aeval (R := k) ↿b).comp θ = f := by
    refine algHom_ext fun l ↦ ?_
    simp only [θ, AlgHom.comp_apply, aeval_X, aeval_rename]
    exact congrFun hΛb l
  refine .tower_top θ.toRingHom _ ?_
  change ((aeval (R := k) ↿b).comp θ).toRingHom.IsIntegral
  rw [hfactor]
  exact hf_fin.to_isIntegral

/-- Let `t` be transcendental over `L`, `j : B → Ω` a map of `k`-algebras with zero kernel, and each
tuple `t⁻¹ • j ∘ b σ` integral over `L`. Let `B` be finite over `k[X₀, …, X_d]` by `f`, with
`Λ` taking `b σ₀` to `f ∘ X`. Then for every map `φ` from `B` to an algebraically closed field
and every `u`, some map `χ` from `B` has `χ ∘ b σ = u • φ ∘ b σ` for all `σ`. -/
private lemma exists_algHom_comp_eq_smul {G B K Ω : Type} [CommRing B] [Algebra k B] [Field K]
    [IsAlgClosed K] [Algebra k K] [Field Ω] [Algebra L Ω] [Algebra k Ω] [IsScalarTower k L Ω]
    {t : Ω} (ht : Transcendental L t) (ht_ne : t ≠ 0) (j : B →ₐ[k] Ω)
    (hj_ker : ∀ r : B, j r = 0 → r = 0) (b : G → ι → B)
    (hw_int : ∀ (σ : G) (i : ι), IsIntegral L ((t⁻¹ • j ∘ b σ) i))
    (f : MvPolynomial (Fin (d + 1)) k →ₐ[k] B) (hf_fin : f.toRingHom.Finite) (σ₀ : G)
    (hΛb : evalForms Λ (b σ₀) = f ∘ X) (φ : B →ₐ[k] K) (u : K) :
    ∃ χ : B →ₐ[k] K, ∀ σ : G, χ ∘ b σ = u • φ ∘ b σ := by
  -- `j ∘ b = t • w` with `w` integral over `L`, so every relation of `b` holds for `u • φ ∘ b`;
  -- as `B` is integral over the polynomials `Λ` in the `b σ₀ i`, `χ` extends `u • φ ∘ b`.
  let w : G × ι → integralClosure L Ω := fun (σ, i) ↦ ⟨_, hw_int σ i⟩
  have hw : t • toAlgHom k (integralClosure L Ω) Ω ∘ w = j ∘ ↿b := by
    funext ⟨σ, i⟩
    exact mul_inv_cancel_left₀ ht_ne _
  have hker : ker (aeval (R := k) ↿b) ≤ ker (aeval (R := k) (u • φ ∘ ↿b)) :=
    ker_aeval_le_ker_aeval_smul_of_transcendental ht j hj_ker ↿b w hw φ u
  obtain ⟨χ, hχ⟩ : ∃ χ : B →ₐ[k] K, χ.comp (aeval ↿b) = aeval (u • φ ∘ ↿b) :=
    exists_algHom_comp_eq_of_integral _ _ (isIntegral_aeval_of_evalForms_eq f hf_fin b σ₀ hΛb) hker
  refine ⟨χ, fun σ ↦ funext fun i ↦ ?_⟩
  simpa [Function.HasUncurry.uncurry] using DFunLike.congr_fun hχ (X (σ, i))

variable [CharZero k] [Finite ι]

/-- The Galois closure of a Noether normalisation `Λ` of a finite tuple `g`: a finite group `G`, a
finite injective map `f : k[X₀, …, X_d] → B` of `k`-algebras and tuples `b σ` over `B`, `σ ∈ G`, on
the cone of `g`, that `Λ` takes to the variables and that `G` permutes up to proportionality. -/
structure IsNoetherNormalization.GaloisClosure (Λ : Fin (d + 1) → homogeneousSubmodule ι k 1)
    (g : ι → L) where
  /-- The finite group that permutes the tuples `b σ`. -/
  G : GrpCat.{0}
  /-- The algebra over `k[X₀, …, X_d]` in which the tuples lie. -/
  B : CommAlgCat k
  /-- The group `G` is finite. -/
  fintype : Fintype G
  /-- The map from `k[X₀, …, X_d]`. -/
  f : MvPolynomial (Fin (d + 1)) k →ₐ[k] B
  /-- The tuples, indexed by `G`. -/
  b : G → ι → B
  /-- Each `b σ` lies on the cone of `g`. -/
  isHomogeneousSolution (σ : G) : IsHomogeneousSolution k g (b σ)
  /-- The forms `Λ` take each `b σ` to the variables: `Λ j (b σ) = f (X j)`. -/
  evalForms_eq (σ : G) : evalForms Λ (b σ) = f ∘ X
  /-- The map `f` is finite. -/
  finite : f.toRingHom.Finite
  /-- The map `f` is injective. -/
  injective : Injective f
  /-- If `φ`, `ψ` map `B` to an algebraically closed field and `ψ (f (X j)) = u φ (f (X j))` for
  all `j`, then for some `τ ∈ G`, `ψ (b σ) = u φ (b (τ σ))` for all `σ`. -/
  exists_shift {K : Type} [Field K] [IsAlgClosed K] [Algebra k K] (φ ψ : B →ₐ[k] K) (u : K) :
    u • φ ∘ f ∘ X = ψ ∘ f ∘ X → ∃ τ : G, ∀ σ : G, ψ ∘ b σ = u • φ ∘ b (τ * σ)

/-- A Noether normalisation `Λ` of a finite tuple `g` with entries in a field `L`, over a field `k`
of characteristic zero, has a Galois closure
(`New.Variety.CutsOutLocus.IsNoetherNormalization.GaloisClosure`). -/
lemma IsNoetherNormalization.nonempty_galoisClosure (hΛ : IsNoetherNormalization Λ g) :
    Nonempty (IsNoetherNormalization.GaloisClosure Λ g) := by
  -- Take `t` transcendental over `L`. The values of `Λ` at `t • g` are algebraically independent,
  -- so they embed `A = k[X]` in an algebraically closed field `Ω`, and `t • g` is integral over
  -- `A`. `B` is a Galois hull of `t • g` over `A` and the `b σ` are the conjugates of `t • g`.
  obtain ⟨h_no_rel, h_integral⟩ := hΛ
  let Ω : Type := AlgebraicClosure (RatFunc L)
  let inc : L →ₐ[k] Ω := toAlgHom k L Ω
  let A : Type := MvPolynomial (Fin (d + 1)) k
  obtain ⟨t, ht⟩ : ∃ t : Ω, Transcendental L t :=
    ⟨_, (transcendental_algebraMap_iff (algebraMap_injective _ Ω)).mpr RatFunc.transcendental_X⟩
  have ht_ne : t ≠ 0 := by simpa using not_exists.mp ht .X
  have h_tg : IsHomogeneousSolution k g (t • inc ∘ g) := .smul inc t .refl
  algebraize [(aeval (R := k) (evalForms Λ (t • inc ∘ g))).toRingHom]
  -- The values of `Λ` at `t • g` are `t` times those at `g`, which satisfy no nonzero homogeneous
  -- relation. (`using!`: the algebra instance comes from `algebraize`.)
  have h_faithful : FaithfulSMul A Ω := by
    refine (faithfulSMul_iff_algebraMap_injective A Ω).mpr
      (algebraicIndependent_iff.mpr fun F ↦ ?_)
    simpa [aeval_X_left_apply] using! h_no_rel.aeval_eq_zero_of_transcendental ht
  have h_forms_X : evalForms Λ (t • inc ∘ g) = aeval (R := k) (evalForms Λ (t • inc ∘ g)) ∘ X :=
    funext fun l ↦ (aeval_X _ l).symm
  have h_int (i : ι) : IsIntegral A ((t • inc ∘ g) i) := h_integral (aeval _) X _ h_tg h_forms_X i
  -- `incA : B → Ω` is an injective `A`-algebra map with `incA ∘ x = t • inc ∘ g`
  obtain ⟨B, fintypeGal, incA, x, hinv, hfin, h_incA_inj, h_incA_x⟩ := exists_galois_hull h_int
  algebraize [(algebraMap A B).comp C]
  let j : B →ₐ[k] Ω := incA.restrictScalars k
  let f : A →ₐ[k] B := toAlgHom k A B
  have hjf : j ∘ f ∘ X = evalForms Λ (t • inc ∘ g) :=
    funext fun i ↦ (incA.commutes _).trans (aeval_X _ i)
  let b (σ : Gal(B/A)) : ι → B := σ.toAlgHom.restrictScalars k ∘ x
  -- `h_incA_x` with `j`, the form that the rewrites below need
  have h_jx : j ∘ x = t • inc ∘ g := h_incA_x
  have hj_ker : ∀ r : B, j r = 0 → r = 0 := fun r hr ↦ h_incA_inj (hr.trans (map_zero incA).symm)
  have hb (σ : Gal(B/A)) : IsHomogeneousSolution k g (b σ) :=
    .of_ker j _ (fun r hr ↦ by rw [hj_ker r hr, map_zero]) (by rwa [h_jx])
  have hx_forms : evalForms Λ x = f ∘ X := by
    apply h_incA_inj.comp_left
    calc incA ∘ evalForms Λ x = evalForms Λ (j ∘ x) := (evalForms_map Λ j x).symm
      _ = incA ∘ f ∘ X := by rw [h_jx]; exact hjf.symm
  -- `σ` fixes the image of `A`
  have hΛb (σ : Gal(B/A)) : evalForms Λ (b σ) = f ∘ X := by
    rw [evalForms_map, hx_forms]
    exact funext fun i ↦ σ.commutes (X i)
  have hf_inj : Injective f := .of_comp (f := incA) fun a a' h ↦
    algebraMap_injective A Ω <| by simpa [f] using h
  refine ⟨{
    G := .of Gal(B/A), B := .of k B, fintype := inferInstance, f := f, b := b,
    isHomogeneousSolution := hb, evalForms_eq := hΛb, finite := hfin, injective := hf_inj,
    exists_shift := fun {K _ _ _} φ ψ u hu ↦ ?_ }⟩
  -- Dividing by `t`: `t⁻¹ • j ∘ b σ` is integral over `L`, since `Λ` has values in `L` there.
  have hw_int (σ : Gal(B/A)) (i : ι) : IsIntegral L ((t⁻¹ • j ∘ b σ) i) := by
    refine h_integral inc (evalForms Λ g) _ ((hb σ).smul j t⁻¹) ?_ i
    simp [hΛb, hjf, ht_ne]
  -- So scaling `φ ∘ b` by `u` is induced by a map `χ` on `B`; it agrees with `ψ` on `A`.
  obtain ⟨χ, hχb⟩ : ∃ χ : B →ₐ[k] K, ∀ σ : Gal(B/A), χ ∘ b σ = u • φ ∘ b σ :=
    exists_algHom_comp_eq_smul ht ht_ne j hj_ker b hw_int f hfin 1 (hΛb 1) φ u
  have hχf : χ ∘ f ∘ X = u • φ ∘ f ∘ X := by
    simpa [hΛb] using congrArg (evalForms Λ) (hχb 1)
  have h_agree : χ.comp f = ψ.comp f := algHom_ext (congrFun (hχf.trans hu))
  obtain ⟨τ, hτ⟩ : ∃ τ : Gal(B/A), ∀ a : B, ψ a = χ (τ a) := exists_algEquiv_of_comp_eq hinv h_agree
  refine ⟨τ, fun σ ↦ ?_⟩
  rw [← hχb (τ * σ)]
  exact funext fun i ↦ hτ (b σ i)

/-- The Galois closure of a Noether normalisation `Λ` of a finite tuple `g` with entries in a field
`L`, over a field `k` of characteristic zero. There are a finite group `G`, a map of `k`-algebras
`f : k[X₀, …, X_d] → B` and tuples `b σ` over `B`, `σ ∈ G`, such that: (a) each `b σ` lies on the
cone of `g`, and `Λ j` takes the value `f (X j)` at it; (b) `f` is finite and injective; (c) if `φ`,
`ψ` map `B` to an algebraically closed field and `ψ (f (X j)) = u φ (f (X j))` for all `j`, then for
some `τ ∈ G` we have `ψ (b σ) = u φ (b (τ σ))` for all `σ`. -/
lemma IsNoetherNormalization.exists_galois_closure (hΛ : IsNoetherNormalization Λ g) :
    ∃ (G : GrpCat.{0}) (B : CommAlgCat k) (_ : Fintype G)
        (f : MvPolynomial (Fin (d + 1)) k →ₐ[k] B)
        (b : G → ι → B),
      -- (a)
      (∀ σ : G, IsHomogeneousSolution k g (b σ) ∧ evalForms Λ (b σ) = f ∘ X) ∧
      -- (b)
      f.toRingHom.Finite ∧ Injective f ∧
      -- (c)
      ∀ {K : Type} [Field K] [IsAlgClosed K] [Algebra k K] (φ ψ : B →ₐ[k] K) (u : K),
        u • φ ∘ f ∘ X = ψ ∘ f ∘ X → ∃ τ : G, ∀ σ : G, ψ ∘ b σ = u • φ ∘ b (τ * σ) := by
  obtain ⟨⟨G, B, fintypeG, f, b, hb_hom, hb_lv, h_fin, h_inj, h_conj⟩⟩ :=
    hΛ.nonempty_galoisClosure
  exact ⟨G, B, fintypeG, f, b, fun σ ↦ ⟨hb_hom σ, hb_lv σ⟩, h_fin, h_inj, h_conj⟩

end New.Variety.CutsOutLocus

end NoetherNormalization

/-!
## Homogeneous coordinates of points of an embedded variety

Points of a scheme Y over Spec R with values in k-algebras A (`New.Variety.PointsIn`) are described
by homogeneous coordinates for a line bundle L that embeds Y (`New.LineBundle.IsProjEmbedding`,
finite index set ι).
-/

namespace New.Variety

open CategoryTheory Function AlgebraicGeometry MvPolynomial CutsOutLocus CommAlgCat ProjSpace Ideal
  Over Category

variable {k ι : Type} {F : Type} [Field k]
  {R : CommRingCat} [Algebra R.carrier k] {Y : Over (Spec R)}
  (L : LineBundle Y.left ι) {A B : CommAlg k} (x x' : PointsIn Y A)
  (v : ι → A) [Field F] [Algebra k F] [hL : Fact (L.IsProjEmbedding Y.hom)]

/-- The vector v in A^ι is a vector of homogeneous coordinates, for L, of the A-point x of Y,
and some coordinate v_i is a unit. -/
abbrev IsCoordsWithUnit : Prop := L.IsHomogeneousCoords x.down.left v ∧ ∃ i : ι, IsUnit (v i)

/-- If étale charts of dimension d cover Y (`IsChartCovered`), a point x over a field comes, along
some κ, from the universal point of such a chart that has coordinates with a unit entry. -/
lemma IsCoordsWithUnit.exists_chart_coords (hK : IsField A) {d : ℕ}
    [IsChartCovered d (algPointsOf k R Y)] :
    ∃ (c : EtaleChart d (algPointsOf k R Y)) (κ : c.coordRing ⟶ A) (w : ι → c.coordRing),
      PointsIn.map κ c.point = x ∧ IsCoordsWithUnit L c.point w := by
  -- `x` lands in some `L.opens i`. Shrink a chart around `x` into that open set; there the
  -- functions `L.transition i j` are homogeneous coordinates whose `i`-th entry is a unit.
  let fieldA : Field A := hK.toField
  obtain ⟨i, hi⟩ : ∃ i : ι, LandsIn x.down.left (L.opens i) := L.exists_landsIn x.down.left
  -- The points that land in `L.opens i` form an open subfunctor `U`, which contains `x`.
  let U : Subfunctor (algPointsOf k R Y) :=
    ⟨fun _ ↦ {y | LandsIn y.down.left (L.opens i)}, by tauto⟩
  -- Along `ψ : A ⟶ B` the point `PointsIn.map ψ y` is `Spec ψ` followed by `y`.
  have h_map_left : ∀ (A B : CommAlg k) (ψ : A ⟶ B) (y : PointsIn Y A),
      (PointsIn.map ψ y).down.left = specMap ψ.hom ≫ y.down.left := by tauto
  have hU : IsOpenSubfunctor U :=
    isOpenSubfunctor_of_landsIn (fun y ↦ y.down.left) h_map_left U fun _ _ ↦ .rfl
  obtain ⟨c, ⟨κ, hκ⟩, hc⟩ := hU.exists_mem_locus_and_point_mem hK hi
  have h_coords : L.IsHomogeneousCoords c.point.down.left
      (fun j : ι ↦ L.transition i j _ c.point.down.left) :=
    hL.out.isLinearSystem.isHomogeneousCoords_transition hc
  exact ⟨c, _, fun j ↦ L.transition i j _ c.point.down.left, hκ, h_coords, i,
    L.isUnit_transition hc hc⟩

variable {L x x' v} {ξ : PointsIn Y (of k F)} {g : ι → of k F} {i : ι}

omit [Fact (L.IsProjEmbedding Y.hom)] in
/-- Two vectors of coordinates with a unit entry of the same point `x` differ by a unit of `A`. -/
lemma IsCoordsWithUnit.exists_unit_smul_eq {w : ι → A} (hv : IsCoordsWithUnit L x v)
    (hw : IsCoordsWithUnit L x w) :
    ∃ u : Aˣ, u • v = w := by
  -- The unit is `w i / v i`, for a coordinate `v i` that is a unit; `w i` is a unit too, as `x`
  -- lands in `L.opens i`.
  obtain ⟨hv_coords, i, hvi⟩ := hv
  obtain ⟨hv_lands_iff, hv_transition⟩ := hv_coords i
  obtain ⟨hw_lands_iff, hw_transition⟩ := hw.left i
  have hwi : IsUnit (w i) := hw_lands_iff.mp (hv_lands_iff.mpr hvi)
  refine ⟨(hvi.ringInverse.mul hwi).unit, funext fun j ↦ ?_⟩
  -- Both `v j / v i` and `w j / w i` are the value of the chart function `L.transition i j` at `x`.
  have h_chart : v j * Ring.inverse (v i) = w j * Ring.inverse (w i) :=
    (hv_transition j hvi).symm.trans (hw_transition j hwi)
  calc Ring.inverse (v i) * w i * v j = v j * Ring.inverse (v i) * w i := by ring
    _ = w j := by rw [h_chart, Ring.inverse_mul_cancel_right _ _ hwi]

/-- If `v` is a vector of coordinates with a unit entry of `x`, `φ : A ⟶ B` is a map of
`k`-algebras and `u` is a unit of `B`, then `u • φ ∘ v` is a vector of coordinates with a unit entry
of the image of `x` under `φ`. -/
lemma IsCoordsWithUnit.map_unit_smul (hv : IsCoordsWithUnit L x v) (φ : A ⟶ B) (u : Bˣ) :
    IsCoordsWithUnit L (x.map φ) (u • φ ∘ v) := by
  obtain ⟨h_lifts, i, hi⟩ := hv
  -- the coordinates map along `φ` and scale by `u`; the entry `i` stays a unit
  have h_coords : L.IsHomogeneousCoords (x.map φ).down.left (u • φ ∘ v) :=
    (h_lifts.map hL.out.isLinearSystem hi _).smul u.isUnit
  exact ⟨h_coords, i, u.isUnit.mul (hi.map φ.hom)⟩

lemma IsCoordsWithUnit.comp (h : IsCoordsWithUnit L x v) (φ : A ⟶ B) :
    IsCoordsWithUnit L (x.map φ) (φ ∘ v) := by
  simpa using h.map_unit_smul φ 1

/-- Two `A`-points of `Y` with the same vector `v` of coordinates with a unit entry are equal. -/
lemma IsCoordsWithUnit.ext (h : IsCoordsWithUnit L x v) (H : IsCoordsWithUnit L x' v) :
    x = x' := by
  -- `L` is an embedding: two points over the base with the same coordinates agree.
  obtain ⟨hx_coords, i, hvi⟩ := h
  obtain ⟨hx'_coords, -⟩ := H
  have h_base : x.down.left ≫ Y.hom = x'.down.left ≫ Y.hom :=
    (Over.w x.down).trans (Over.w x'.down).symm
  have h_lands : LandsIn x.down.left (L.opens i) := ((hx_coords i).left).mpr hvi
  have h_left : x.down.left = x'.down.left :=
    hL.out.eq_of_isHomogeneousCoords h_base hx_coords hx'_coords ⟨i, h_lands⟩
  exact ULift.down_injective (OverMorphism.ext h_left)

/-! ### Points over a field: descent, spreading out and specialisation -/

variable [Finite ι]

/-- Descent. Let ξ be a point over a field F with coordinates g, and φ : A → F injective. If
g = g_i φ(v) for a vector v over A, then ξ comes from a point over A with coordinates v. -/
lemma IsCoordsWithUnit.exists_descend_of_injective (hξ : IsCoordsWithUnit L ξ g) (φ : A ⟶ of k F)
    (φ_inj : Function.Injective φ) (h_coord : g i • φ ∘ v = g) :
    ∃ x : PointsIn Y A, IsCoordsWithUnit L x v ∧ ξ = x.map φ := by
  -- View `Y` as a closed subscheme of projective space. The vector `v` gives a point `t` of
  -- projective space over `A` with image `ξ` under `φ`; as `φ` is injective, `t` lies in `Y`.
  -- Some entry `g l = g i * φ (v l)` is a unit, so `g i` is a unit; then `g i * φ (v i) = g i`
  -- gives `v i = 1`.
  obtain ⟨l, hgl_unit⟩ : ∃ l : ι, IsUnit (g l) := hξ.right
  have hgi_unit : IsUnit (g i) := by
    rw [← congrFun h_coord l] at hgl_unit
    exact isUnit_of_mul_isUnit_left hgl_unit
  have hvi : v i = 1 :=
    (map_eq_one_iff _ φ_inj).mp (hgi_unit.mul_eq_left.mp (congrFun h_coord i))
  have hv : IsUnit (v i) := by simp [hvi]
  obtain ⟨j, _, hj, rfl⟩ := hL.out.exists_isClosedImmersion
  obtain ⟨t, ht_over, ht⟩ := exists_isHomogeneousCoords (Opposite.unop ((specAlg k R).obj A)).hom hv
  -- `ξ` and the image of `t` both have coordinates `g` and lie over the same point of `Spec R`.
  have h_image : ξ.down.left ≫ j = Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫ t := by
    have h_coords_image : LineBundle.IsHomogeneousCoords ((hyperplaneBundle ι).pull Limits.prod.fst)
        (Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫ t) g :=
      h_coord ▸ (ht.map (isLinearSystem_hyperplaneBundle.pull _) hv _).smul hgi_unit
    refine isProjEmbedding_projSpace.eq_of_isHomogeneousCoords ?_ hξ.left h_coords_image
      (LineBundle.exists_landsIn _ _)
    let u := ((specAlg k R).map φ).unop
    change (ξ.down.left ≫ j) ≫ Limits.prod.snd = (u.left ≫ t) ≫ Limits.prod.snd
    calc
      _ = ξ.down.left ≫ Y.hom :=
        (assoc ..).trans (congrArg (ξ.down.left ≫ ·) hj)
      _ = u.left ≫ (t ≫ Limits.prod.snd) :=
        ξ.down.w.trans (u.w.symm.trans (congrArg (u.left ≫ ·) ht_over).symm)
      _ = _ := (assoc ..).symm
  -- The ideal `J` cutting out the locus where `t` lies in `Y` is killed by `φ`, hence is zero.
  obtain ⟨J, -, hJ⟩ := exists_ideal_le_ker_iff_factors j t
  have h_ker_le : RingHom.ker φ.hom.toRingHom ≤ RingHom.ker (RingHom.id A) :=
    ((RingHom.injective_iff_ker_eq_bot _).mp φ_inj).le.trans bot_le
  have hJ0 : J ≤ RingHom.ker (RingHom.id A) :=
    ((hJ φ.hom.toRingHom).mpr ⟨ξ.down.left, h_image⟩).trans h_ker_le
  obtain ⟨x, rfl⟩ : ∃ x : Spec (CommRingCat.of A) ⟶ Y.left, x ≫ j = t := by
    simpa using (hJ (RingHom.id A)).mp hJ0
  -- `x` lies over `Spec R`, since `x ≫ j` does
  have h_x_over : x ≫ Y.hom = (Opposite.unop ((specAlg k R).obj A)).hom := by
    rw [← hj, ← Category.assoc]
    exact ht_over
  let y : PointsIn Y A := ⟨homMk x h_x_over⟩
  have hx : IsCoordsWithUnit (((hyperplaneBundle ι).pull Limits.prod.fst).pull j) y v :=
    ⟨ht, i, hv⟩
  -- The image of `y` under `φ` has coordinates `g i • φ ∘ v = g`, as `ξ` has.
  have hx_map : IsCoordsWithUnit (((hyperplaneBundle ι).pull Limits.prod.fst).pull j)
      (PointsIn.map φ y) g := by
    simpa [← Units.smul_def, h_coord] using hx.map_unit_smul φ hgi_unit.unit
  exact ⟨_, hx, hξ.ext hx_map⟩

/-- Spreading out. Let ξ be a point over a field F with coordinates g, and let v_i ≠ 0 for some v
satisfying the homogeneous relations of g. Then there are a k-algebra D, a point y over D, a map j :
D → F and polynomials G_d (d ∈ D) with two properties. (a) j is injective and ξ = j(y). (b) Let w
over a k-algebra C satisfy the homogeneous relations of g, with w_i a unit. Then some φ : D → C has
φ(d) associated to G_d(w) for all d, and φ(y) has coordinates w. -/
lemma IsCoordsWithUnit.exists_universal_chart (hξ : IsCoordsWithUnit L ξ g)
    (hv : CutsOutLocus.IsHomogeneousSolution k g v) (hvi : v i ≠ 0) :
    ∃ (D : CommAlgCat k) (y : PointsIn Y D), ∃ (j : D ⟶ of k F) (G : D → MvPolynomial ι k),
      -- (a)
      (Function.Injective j ∧ ξ = PointsIn.map j y) ∧
      -- (b)
      ∀ {C : CommAlgCat k} {w : ι → C},
        CutsOutLocus.IsHomogeneousSolution k g w →
        IsUnit (w i) →
        ∃ φ : D ⟶ C,
          (∀ d : D, Associated (aeval w (G d)) (φ d)) ∧ IsCoordsWithUnit L (y.map φ) w := by
  -- `D` is the coordinate ring of the affine chart `X i = 1`: polynomials modulo those vanishing at
  -- `(g i)⁻¹ • g`. Homogeneous relations of `g` hold for `w`, so evaluation at `(w i)⁻¹ • w`
  -- factors through `D`.
  have hgi : IsUnit (g i) := by simpa [hvi] using hv (isHomogeneous_X _ i)
  -- `homog P` is homogeneous (`h_homog_deg`) and agrees with `P` under algebra maps with `X i ↦ 1`
  -- (`h_chart`).
  have h_homog (P : MvPolynomial ι k) : ∃ G : MvPolynomial ι k, G.IsHomogeneous P.totalDegree ∧
      ∀ {A : Type} [CommRing A] [Algebra k A] (φ : MvPolynomial ι k →ₐ[k] A),
        φ (X i) = 1 → φ G = φ P :=
    exists_homogenization (isHomogeneous_X k i) P le_rfl
  choose homog h_homog_deg h_chart using h_homog
  -- Evaluation at `(w i)⁻¹ • w` agrees up to a unit with evaluating the homogenisation at `w`.
  have h_eval {C : CommAlg k} {w : ι → C} (u : IsUnit (w i)) :
      ∃ φ : MvPolynomial ι k →ₐ[k] C,
        w i • φ ∘ X = w ∧ ∀ P, Associated ((homog P).aeval w) (φ P) := by
    refine ⟨aeval (u.unit⁻¹.val • w), by simp [← mul_assoc, funext_iff], fun P ↦ ?_⟩
    simp [← h_chart P, (h_homog_deg _).aeval_smul_of_algebra, smul_eq_mul,
      associated_unit_mul_right, IsUnit.pow]
  -- (`@` keeps `C` and `w` implicit in the chosen functions)
  choose φ hφX hφG using @h_eval
  -- `D = k[X] / ker (φ hgi)` embeds in `F`, so `ξ` descends to `y` with coordinates `X` mod kernel.
  obtain ⟨y, hy, hξy⟩ :=
    hξ.exists_descend_of_injective (ofHom _) (kerLiftAlg_injective (φ hgi)) (v := fun l ↦ ⟦X l⟧)
      (hφX hgi)
  refine ⟨.of k (MvPolynomial ι k ⧸ RingHom.ker (φ hgi)), y, ofHom (kerLiftAlg (φ hgi)),
    fun d ↦ homog d.out, ⟨kerLiftAlg_injective _, hξy⟩, fun hw u ↦ ?_⟩
  have h_ker (P : MvPolynomial ι k) (hP : P ∈ RingHom.ker (φ hgi)) : φ u P = 0 :=
    (hφG u P).eq_zero_iff.mp (hw (h_homog_deg P) ((hφG hgi P).eq_zero_iff.mpr hP))
  refine ⟨ofHom (Quotient.liftₐ _ (φ u) h_ker), fun d ↦ ?_, ?_⟩
  · conv_rhs => rw [← Quotient.out_eq d]
    exact hφG u d.out
  · -- The image of `y` has coordinates `w i • φ u ∘ X = w`. (`rw` cannot replace `w` here, as
    -- `φ u` depends on it.)
    exact (hφX u).subst (hy.map_unit_smul _ u.unit)

/-- Let `Y` be a scheme over `Spec R` with a line bundle `L` embedding it in projective space, and
let `k` be an algebraically closed `R`-algebra. Let `ξ` be an `F`-point of `Y` over a field `F ⊇ k`
with `L`-coordinates `g`, one of them a unit, and let `f` be a map from the functor `A ↦ Y(A)` on
`k`-algebras to the affine line. Then there is `c ∈ k` such that `f(x) = c` for every point
`x ∈ Y(A)` over a nonzero `k`-algebra `A` whose `L`-coordinates `v` have a unit entry and lie on the
cone of `g`, i.e. every homogeneous polynomial over `k` vanishing at `g` vanishes at `v`. -/
lemma IsCoordsWithUnit.exists_app_eq_algebraMap_of_isHomogeneousSolution
    (hξ : IsCoordsWithUnit L ξ g) [IsAlgClosed k] (f : algPointsOf k R Y ⟶ affineSpace k 1) :
    ∃ c : k, ∀ {A : CommAlg k} [Nontrivial A] {x : PointsIn Y A} {v : ι → A},
      IsCoordsWithUnit L x v →
      CutsOutLocus.IsHomogeneousSolution k g v → (f A x).down 0 = algebraMap k A c := by
  have h_nonempty : Nonempty ι := hξ.right.nonempty
  have h_f_map {A B : CommAlg k} (φ : A ⟶ B) (y : PointsIn Y A) :
      (f.app B (PointsIn.map φ y)).down 0 = φ ((f.app A y).down 0) :=
    congrArg (fun a ↦ a.down 0) (f.naturality_apply φ y)
  -- The value at `ξ` lies in every valuation ring `V` over `k`: dividing by the coordinate of
  -- largest valuation shows that `ξ` comes from a point over `V`. So it is integral over `k`.
  have h_integral : (algebraMap k F).IsIntegralElem ((f.app _ ξ).down 0) := by
    refine isIntegralElem_of_valuationSubring fun V hV ↦ ?_
    have h_max : ∃ i : ι, ∀ l : ι, ∃ x : V, x • g i = g l := Finite.exists_max (V.valuation ∘ g)
    choose i w hw using h_max
    -- the inclusion of `V`, as a subalgebra of `F`
    let toF : of k (⟨V.toSubsemiring, hV⟩ : Subalgebra k F) ⟶ of k F :=
      ofHom (Subalgebra.val ⟨V.toSubsemiring, hV⟩)
    have h_scaled : g i • ⇑toF ∘ w = g := funext fun l ↦ (mul_comm _ _).trans (hw l)
    obtain ⟨y, -, rfl⟩ := hξ.exists_descend_of_injective toF Subtype.val_injective h_scaled
    rw [h_f_map]
    exact Subtype.prop _
  -- As `k` is algebraically closed, this value is a constant `c`.
  obtain ⟨c, hc⟩ : ∃ c, algebraMap k F c = (f.app _ ξ).down 0 :=
    IsAbsIntegrallyClosed.mem_range_of_isIntegralElem h_integral
  refine ⟨c, fun {A} _ {x v} hx hv ↦ ?_⟩
  -- Both `ξ` and `x` are images of one point `y` over `D`, and `j : D ⟶ F` is injective.
  obtain ⟨i, hvi⟩ : ∃ i : ι, IsUnit (v i) := hx.right
  obtain ⟨D, y, j, G, ⟨j_inj, rfl⟩, h_spec⟩ := hξ.exists_universal_chart hv hvi.ne_zero
  obtain ⟨φ, -, hφ⟩ := h_spec hv hvi
  have h_f_y : (f.app D y).down 0 = algebraMap k D c :=
    j_inj ((h_f_map j y).symm.trans <| hc.symm.trans (j.hom.commutes c).symm)
  rw [hx.ext hφ, h_f_map, h_f_y]
  exact φ.hom.commutes c

/-- Let ξ be a point over a field F with coordinates g, lying in an open subfunctor V. Some
polynomial b with b(g) ≠ 0 has the property: every w that satisfies the homogeneous relations
of g and makes b(w) a unit is a vector of coordinates of a point of V. -/
lemma IsCoordsWithUnit.exists_mem_open_of_isUnit (hξ : IsCoordsWithUnit L ξ g)
    {V : Subfunctor (algPointsOf k R Y)} (hV : IsOpenSubfunctor V) (hξV : ξ ∈ V (of k F)) :
    ∃ b : MvPolynomial ι k,
      aeval g b ≠ 0 ∧
      ∀ {C : CommAlg k} {w : ι → C},
        CutsOutLocus.IsHomogeneousSolution k g w →
        IsUnit (aeval w b) →
        ∃ z ∈ V C, IsCoordsWithUnit L z w := by
  -- Spread `ξ` out to a point `z` over a subalgebra `D` of `F`; openness of `V` gives `b ∈ D` whose
  -- invertibility forces the specialisations of `z` into `V`. Take the polynomial `G b * X i`.
  obtain ⟨i, hi⟩ : ∃ i : ι, IsUnit (g i) := hξ.right
  obtain ⟨D, z, -, G, -, h_spec⟩ := hξ.exists_universal_chart .refl hi.ne_zero
  -- `z` specialises to `ξ` itself along `φ₀`, so this specialisation lies in `V`
  obtain ⟨φ₀, hφ₀, h_gen⟩ := h_spec .refl hi
  have h_eq : z.map φ₀ = ξ := h_gen.ext hξ
  have hz : z.map φ₀ ∈ V.obj _ := by rwa [h_eq]
  obtain ⟨b, hb, h_open⟩ := hV.exists_basicOpen φ₀ z (Field.toIsField _) hz
  refine ⟨G b * X i, ?_, fun hw h_unit ↦ ?_⟩
  · have h_Gb : aeval g (G b) ≠ 0 := (hφ₀ b).ne_zero_iff.mpr hb
    simpa using mul_ne_zero h_Gb hi.ne_zero
  · rw [map_mul, aeval_X, IsUnit.mul_iff] at h_unit
    obtain ⟨h_Gb_unit, h_wi_unit⟩ := h_unit
    obtain ⟨φ, hφ, h_coord⟩ := h_spec hw h_wi_unit
    exact ⟨z.map φ, h_open _ φ ((hφ b).isUnit h_Gb_unit), h_coord⟩

end New.Variety
