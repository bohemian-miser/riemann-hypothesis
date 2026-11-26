module

import Mathlib.Algebra.GroupWithZero.Torsion
import Mathlib.Algebra.Order.Monoid.Unbundled.Units
import TauCeti.NumberTheory.NumberField.Quadratic.ChowlaSelberg
import TauCeti.NumberTheory.NumberField.Quadratic.DedekindZeta
public import Lib.CM.ConjugateCurve
public import Lib.General.Algebra.AdicCompletion
import Lib.Analytic.EntireLFunction
import Lib.CM.Integrality.IsogenyIntegrality
import Lib.ClassField.Places.ValuationSubrings
import Lib.General.NumberTheory.EmbeddingsAndDifferent

/-!
# Odd class number, ζ_K = ζ·L(s, χ), theta functions with CM and Chowla–Selberg

Throughout, `K = ℚ(√-d)` (`New.QuadField d`) for a prime `d ≡ 7 mod 8` (`New.PrimeSevenModEight d`),
and `χ` is the Legendre symbol modulo `d`. For such `K` the class number is odd, and the Dedekind
zeta function factors as `ζ_K(s) = ζ(s) L(s, χ)`. The second part treats curves with complex
multiplication by `K`, given by CM lattices `C : New.CMLattice d`. For these curves the file proves
a complex multiplication law for the translates of the theta function when the lattice is `Ω₀ 𝓞_K`,
and the formula of Chowla and Selberg for the areas of the conjugate lattices.

## Main definitions and results

* `New.QuadField.classGroup_sq_bijective`: squaring permutes the class group, that is, the class
  number is odd.
* `TauCeti.NumberField.dedekindZeta_eq_riemannZeta_mul_LFunction`: `ζ_K(s) = ζ(s) L(s, χ)` for
  `Re s > 1`, specialised here to `χ` the Legendre symbol modulo `d`.
* `New.CMLattice.IsComplexMultiplicationData`, `New.CMLattice.complex_multiplication_theta`: the
  action of `σ` on the translates of `θ` by torsion points is given by one finite adele of `K`, if
  the lattice is `Ω₀ 𝓞_K`.
* `TauCeti.NumberField.chowlaSelberg_classMean`: Kronecker's limit formula summed over the class
  group, giving the geometric mean of `exp (UpperHalfPlane.logPeriod τ)`.
* `New.CMLattice.chowla_selberg`: after scaling by the conjugates of one unit, all conjugate
  lattices have the area that this class-group mean gives.

Notions from other files:
* `New.CMLattice`: A lattice `Λ` stable under the integers of `ℚ(√-d)`, with a point `t` of order
  two modulo `Λ` such that `ω t`, `ω̄ t ∉ Λ` for `ω = (1 + √-d) / 2`, scaled so that `℘''(t) = 2`,
  and a square root `a₁` of `12 ℘(t)`; the discriminant of `Λ` is `a₁⁴ - 64`.
* `New.CMLattice.θ`: The twisted translate of the sigma function by `t`, normalised to `1` at `0`.
* `PeriodPair.area`: The area |Im(ω̄₁ω₂)| of the fundamental parallelogram spanned by the periods
  ω₁, ω₂ of a period pair.
* `New.chowlaSelbergConst`: The real number `γ - Re L'/L(1, χ_K)`, with `γ` Euler's constant.

## Relation to the literature

Known result: The class number of an imaginary quadratic field of prime discriminant is odd. Here it
is stated as bijectivity of squaring on the class group, for primes congruent to 7 modulo 8. Source:
C. F. Gauss, Disquisitiones; D. Cox, Primes of the form x²+ny² (1989), §3 and §6.

Known result: The Dedekind zeta function of a quadratic field is the product of the Riemann zeta
function and the L-function of its character, and the sum of the zeta functions of its ideal
classes. Source: J. Neukirch, Algebraic Number Theory (1999), VII.5 and VII.10.

Known result: The formula of Lerch and of Chowla and Selberg for the geometric mean of
area · |disc|^(1/6) over the ideal classes (`TauCeti.NumberField.chowlaSelberg_classMean`). Here the
discriminant is prime with 2 split, and the mean is left in terms of the logarithmic derivative of
the L-function at 1, with no Gamma values. The integrality of isogenies then gives one number, a
unit at every p-adic place, whose conjugates scale all conjugate lattices to this area. Source: A.
Selberg, S. Chowla, On Epstein's zeta-function, J. reine angew. Math. 227 (1967) 86-110; B. Gross,
On the periods of abelian varieties, arXiv 2005.04194.

Known result: The main theorem of complex multiplication for elliptic curves, without the
reciprocity law. It is shown that the conjugate lattice is `Ω 𝔠² / N(𝔠)` and that one finite adele
describes the Galois action on the translates of the theta function by torsion points. The adele is
not identified with the Artin map and is not shown here to be a unit. Source: G. Shimura,
Introduction to the Arithmetic Theory of Automorphic Functions (1971), Thm 5.4; J. Milne, Complex
Multiplication (2020), 9.17.
-/

@[expose] public section

/-!
## The odd class number and the factorisation of ζ_K

* `New.QuadField.eq_d_of_span_eq_sq`: only `d` ramifies in `K`, used directly to prove that the
  class number of `K` is odd (`classGroup_sq_bijective`).

The factorisation `ζ_K(s) = ζ(s) L(s, χ)` is obtained from Tau Ceti's
`TauCeti.NumberField.dedekindZeta_eq_riemannZeta_mul_LFunction` after showing `discr K = -d`.
-/

section QuadraticZeta

open NumberField Ideal ClassGroup Nat Equiv Complex DirichletCharacter

namespace New.QuadField

variable {d : ℕ} [PrimeSevenModEight d]

/-- Only the prime `d` ramifies in `K = ℚ(√-d)`: if the ideal of `𝓞_K` generated by a prime number
`p` is the square of an ideal, then `p = d`. -/
lemma eq_d_of_span_eq_sq {p : ℕ} (hp : Fact p.Prime) (C : Ideal (𝓞 (QuadField d)))
    (hC : span {(p : 𝓞 (QuadField d))} = C ^ 2) :
    p = d := by
  -- `C` divides the different `(sqrtNegDInt d)`, whose square is `(d)`; norms give `p ^ 2 ∣ d ^ 2`.
  have h_dvd : C ∣ differentIdeal ℤ (𝓞 (QuadField d)) :=
    dvd_differentIdeal_of_mem_sq (hC.le (subset_span rfl))
  have h_pow : p ^ Module.finrank ℤ (𝓞 (QuadField d)) ∣
      d ^ Module.finrank ℤ (𝓞 (QuadField d)) := by
    simpa [← hC, different_eq_span_and_adjoin_betaK, Algebra.norm_natCast, span_singleton_pow,
      sqrtNegDInt_sq] using map_dvd absNorm (pow_dvd_pow_of_dvd h_dvd 2)
  exact (prime_dvd_prime_iff_eq hp.out Fact.out).1 <|
    (Nat.pow_dvd_pow_iff Module.finrank_pos.ne').1 h_pow

/-- The class number of `K = ℚ(√-d)` is odd for a prime `d ≡ 7 mod 8`: squaring permutes the class
group.

This is Gauss's genus theory in this case, but proved directly, without that theory, from
`eq_d_of_span_eq_sq` (only `d` ramifies). -/
lemma classGroup_sq_bijective :
    Function.Bijective fun c : ClassGroup (𝓞 (QuadField d)) ↦ c ^ 2 := by
  -- Let `I ^ 2 = (α)`, `n = N I` and `J = (star α + n) * I`. Then `J ^ 2 = (N J)`. Write
  -- `N J = s ^ 2 * r` with `r` squarefree: `(r)` is a square, so only the ramified prime `d` can
  -- divide `r`. Hence `J`, and with it `I`, is principal.
  suffices h_kernel : ∀ c : ClassGroup (𝓞 (QuadField d)), c ^ 2 = 1 → c = 1 from
    ((injective_iff_map_eq_one
      (powMonoidHom (α := ClassGroup (𝓞 (QuadField d))) 2)).2 h_kernel).bijective_of_finite
  refine mk0_surjective.forall.2 ?_
  rintro ⟨I, hI⟩ h_sq
  obtain ⟨α, hα : I ^ 2 = span {α}⟩ := (mk0_eq_one_iff _).1 ((map_pow mk0 _ 2).trans h_sq)
  have hn : I.absNorm ≠ 0 := absNorm_ne_zero_of_nonZeroDivisors ⟨I, hI⟩
  -- Choose the sign of `α` so that `J ≠ 0`: `star α + n = 0 = -star α + n` would give `n = 0`.
  wlog h_ne : star α + I.absNorm ≠ 0 generalizing α with H
  · exact H (-α) (by simp [hα]) (by grind [star_neg, Nat.cast_eq_zero])
  set J : Ideal (𝓞 (QuadField d)) := span {star α + I.absNorm} * I with hJ_def
  have hJ_ne : J.absNorm ≠ 0 := by simp [hJ_def, h_ne, hn]
  obtain ⟨r, s, -, hs_pos : 0 < s, h_norm : s ^ 2 * r = J.absNorm, hr⟩ :=
    sq_mul_squarefree_of_pos hJ_ne.bot_lt
  have hs : s ≠ 0 := hs_pos.ne'
  have hJ : J ^ 2 = span {(s : 𝓞 (QuadField d))} ^ 2 * span {(r : 𝓞 (QuadField d))} := by
    have hα_norm : I.absNorm ^ 2 = α * star α := by simp [← absNorm_span_eq_mul_star, ← hα]
    have hJ_norm : s ^ 2 * r = (star α + I.absNorm) * (α + I.absNorm) * I.absNorm := by
      rw_mod_cast [h_norm]
      simp [hJ_def, absNorm_span_eq_mul_star, -absNorm_span_singleton]
    have hJ_gen : (star α + I.absNorm) ^ 2 * α = s ^ 2 * r := by
      linear_combination -(star α + I.absNorm) * hα_norm - hJ_norm
    simp [hJ_def, hα, span_mul_span, hJ_gen, mul_pow, span_singleton_pow]
  obtain ⟨B, hB⟩ : span {(s : 𝓞 (QuadField d))} ∣ J :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).1 ⟨_, hJ⟩
  -- `(r) = B ^ 2`; a prime factor `p` of `r` is prime to `r / p`, so `(p)` is a square and `p = d`.
  have h_prime {p : ℕ} (hp : p.Prime) : p ∣ r → p = d := by
    rintro ⟨k, rfl⟩
    rw [hB, mul_pow, Nat.cast_mul, ← span_singleton_mul_span_singleton] at hJ
    have h_mul : span {(p : 𝓞 (QuadField d))} * span {(k : 𝓞 (QuadField d))} = B ^ 2 :=
      (mul_left_cancel₀ (pow_ne_zero 2 (by simpa using hs)) hJ).symm
    obtain ⟨C, hC⟩ := exists_eq_pow_of_mul_eq_pow_of_coprime
      ((isCoprime_span_singleton_iff _ _).2 (coprime_of_squarefree_mul hr).cast) h_mul
    exact eq_d_of_span_eq_sq ⟨hp⟩ C hC
  -- So `r` is a power `d ^ m`, and `(r)` is a square: take square roots in `hJ`.
  set m : ℕ := r.primeFactorsList.length
  have hr_span : span {(r : 𝓞 (QuadField d))} = span {sqrtNegDInt d ^ m} ^ 2 := by
    rw [eq_prime_pow_of_unique_prime_dvd hr.ne_zero h_prime, span_singleton_pow, ← pow_mul']
    simp [m, pow_mul, sqrtNegDInt_sq, ← span_singleton_pow]
  have hJ_span : J = span {s * sqrtNegDInt d ^ m} := by
    rwa [hr_span, ← mul_pow, pow_left_inj two_ne_zero, span_singleton_mul_span_singleton] at hJ
  -- The generator of `J` is a multiple `(star α + n) * w`; cancel to get `I = (w)`.
  obtain ⟨w, hw : s * sqrtNegDInt d ^ m = (star α + I.absNorm) * w⟩ :=
    span_singleton_le_span_singleton.1 (hJ_span.ge.trans mul_le_left)
  refine (mk0_eq_one_iff _).2 ⟨w, ?_⟩
  change I = span {w}
  simpa [hJ_def, hw, ← span_singleton_mul_span_singleton, h_ne] using hJ_span

/-- The discriminant of `K = ℚ(√-d)` is `-d` for a prime `d ≡ 7 mod 8`: the different `(√-d)` has
norm `d`, and `K` has a single complex place. -/
private lemma discr_eq_neg : NumberField.discr (QuadField d) = -(d : ℤ) := by
  have h_star : star (sqrtNegDInt d) = -sqrtNegDInt d := by
    simp
    ring
  have h_norm : (span {sqrtNegDInt d}).absNorm = d := by
    refine Nat.cast_injective (R := 𝓞 (QuadField d)) ?_
    rw [absNorm_span_eq_mul_star, h_star, mul_neg, ← sq, sqrtNegDInt_sq, neg_neg]
  have h_abs : (NumberField.discr (QuadField d)).natAbs = d := by
    rw [← absNorm_differentIdeal (QuadField d) (𝓞 (QuadField d)),
      (different_eq_span_and_adjoin_betaK d).1, h_norm]
  have h_places : InfinitePlace.nrComplexPlaces (QuadField d) = 1 := by
    have h_finrank : 2 * InfinitePlace.nrComplexPlaces (QuadField d) = 2 :=
      (IsTotallyComplex.finrank (K := QuadField d)).symm.trans (finrank_eq_two d)
    omega
  have h_mul : (NumberField.discr (QuadField d)).sign *
      (NumberField.discr (QuadField d)).natAbs = NumberField.discr (QuadField d) :=
    Int.sign_mul_natAbs (NumberField.discr (QuadField d))
  rw [NumberField.sign_discr, h_places, pow_one, h_abs] at h_mul
  omega

/-- On `Re s > 1`, the Dedekind zeta function of `K = ℚ(√-d)` is `ζ(s) L(s, χ)`, where
`quadTwist (N := 1) 1 d` is the Legendre character modulo `1 * d`: Tau Ceti's fundamental
discriminant character of `-d ≡ 1 (mod 4)` agrees termwise with the Legendre symbol modulo `d`. -/
private lemma dedekindZeta_eq_riemannZeta_mul {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta (QuadField d) s = riemannZeta s * (quadTwist (N := 1) 1 d).LFunction s := by
  have hd_mod : -(d : ℤ) ≡ 1 [ZMOD 4] := by
    have hd8 : d % 8 = 7 := PrimeSevenModEight.mod_eight
    rw [Int.ModEq]
    omega
  rw [TauCeti.NumberField.dedekindZeta_eq_riemannZeta_mul_LFunction (finrank_eq_two d) hs]
  congr 1
  rw [LFunction_eq_LSeries _ hs, LFunction_eq_LSeries _ hs]
  refine LSeries_congr (fun {n} _ ↦ ?_) s
  rw [← Int.cast_natCast n, MulChar.ringHomComp_apply, Int.coe_castRingHom,
    TauCeti.Multiquadratic.fundamentalDiscriminantChar_intCast, discr_eq_neg,
    TauCeti.kroneckerSym_eq_jacobiSym_natAbs hd_mod, Int.natAbs_neg, Int.natAbs_natCast,
    ← jacobiSym.legendreSym.to_jacobiSym]
  symm
  simpa [Subsingleton.elim ((n : ℤ) : ZMod 1) 1] using quadTwist_apply (N := 1) 1 d n

end New.QuadField

end QuadraticZeta

/-!
## Complex multiplication for theta functions and the Chowla–Selberg formula

A CM lattice `C : New.CMLattice d` is a lattice `Λ ⊂ ℂ` stable under `𝓞_K`, with a point of order
two and a number `a₁`. For `σ` an automorphism of `ℂ` over `K`, `New.CMLattice.galConjugate C σ` is
a CM lattice with the number `σ a₁`. `New.taylorVia σ f` is the Taylor series at `0` of `f` with `σ`
applied to its coefficients, and `C.twistedTranslate 1 y f` is
`z ↦ exp(-π (z ȳ + |y|²/2) / A) f(z + y)`, with `A` the area of `Λ`.
-/

namespace New

open Complex NumberField Real FractionalIdeal Finset Prod QuadField ClassGroup IsAlgClosed Nat

variable {d : ℕ} [PrimeSevenModEight d]

/-- The lattice of a CM lattice `D` is `w 𝔠²` for a nonzero number `w` and a nonzero integral ideal
`𝔠` of `K = ℚ(√-d)`, because every ideal class of `K` is a square. -/
lemma CMLattice.exists_latticeModule_eq_scaledIdeal_sq (D : CMLattice d) :
    ∃ (w : ℂˣ) (𝔠 : nonZeroDivisors (Ideal (𝓞 (QuadField d)))),
      D.latticeModule = scaledIdeal d (w, FractionalIdeal.mk0 (QuadField d) 𝔠 ^ 2) := by
  -- The lattice is `v 𝔞`; take `𝔠` with `𝔠²` in the class of `𝔞`, so that `u 𝔠² / 𝔞` fixes `v 𝔞`.
  obtain ⟨⟨v, 𝔞⟩, hD⟩ := D.exists_latticeModule_eq_scaledIdeal
  obtain ⟨𝔠, h𝔠 : ClassGroup.mk0 𝔠 ^ 2 = .mk _ 𝔞⟩ :=
    classGroup_sq_bijective.surjective.comp mk0_surjective (.mk _ 𝔞)
  have h_class : ClassGroup.mk (QuadField d) (FractionalIdeal.mk0 (QuadField d) 𝔠 ^ 2 / 𝔞) = 1 := by
    rw [map_div, map_pow, ClassGroup.mk_mk0, h𝔠, div_self']
  obtain ⟨u, hu⟩ := exists_eq_scaledIdeal_mul_of_mk_eq_one h_class (scaledIdeal d (v, 𝔞))
  refine ⟨u * v, 𝔠, ?_⟩
  rw [hD, hu, ← map_mul, Prod.mk_mul_mk, div_mul_cancel]

/-- Let `d` be a prime congruent to 7 mod 8 and `K = ℚ(√-d)`. Let the lattice of the CM lattice `C`
be `Ω₀ 𝓞_K`, let `σ` be an automorphism of `ℂ` over `K`, and let the lattice of the conjugate curve
`C.galConjugate σ` contain `Ω e` and lie in `Ω e⁻¹ 𝓞_K`, with `e ≠ 0` natural. There is a finite
adele `β` of `K` such that, for each `x ∈ K` and each `x' ∈ K` close enough to `β x` in the finite
adeles, applying `σ` to the coefficients of the Taylor series at 0 of the degree-1 twisted translate
`z ↦ exp(−π(z·ȳ + |y|²/2)/A)·θ(z + y)` of `C.θ` by `y = x Ω₀` (with `A` the area of the lattice)
gives the Taylor series at 0 of the degree-1 twisted translate of the conjugate curve's `θ` by
`x' Ω`. -/
lemma CMLattice.exists_finAdele_taylorVia_twistedTranslate_theta (C : CMLattice d)
    (σ : Gal(ℂ/QuadField d)) {Ω₀ : ℂˣ} (h₀ : C.latticeModule = scaledIdeal d (Ω₀, 1)) {Ω : ℂ}
    {e : ℕ} (he : e ≠ 0) (hΩ : Ω * e ∈ (C.galConjugate σ).Λ)
    (h_le : ∀ v ∈ (C.galConjugate σ).Λ,
      ∃ a : 𝓞 (QuadField d), Ω * ((a : QuadField d) / e : QuadField d) = v) :
    ∃ β : 𝔸f (QuadField d), ∀ x : QuadField d,
      ∃ U ∈ nhds (β * algebraMap (QuadField d) (𝔸f (QuadField d)) x),
        ∀ x' : QuadField d, algebraMap (QuadField d) (𝔸f (QuadField d)) x' ∈ U →
          taylorVia σ (C.twistedTranslate 1 (x * Ω₀) C.θ) =
            taylorAtZero ((C.galConjugate σ).twistedTranslate 1 (x' * Ω) (C.galConjugate σ).θ) := by
  -- For finite `S ⊂ K` there is a period `Ω * b S` of the conjugate curve such that `σ` takes the
  -- translate by `x Ω₀` to that by `x Ω b S` for `x ∈ S`. The numbers `b S` lie in the compact set
  -- `e⁻¹ Ô` and cluster at some `β`. For `x ∈ K` and `x'` near `β x`, take `S ∋ x` with `b S * x`
  -- as near to `β x`.
  set D : CMLattice d := C.galConjugate σ
  let ι := algebraMap (QuadField d) (𝔸f (QuadField d))
  have h_period (S : Finset (QuadField d)) :
      ∃ b : QuadField d, ι b ∈ (fun z ↦ (e : QuadField d)⁻¹ • z) '' Ô (QuadField d) ∧
        Ω * b ∈ D.Λ ∧ ∀ x ∈ S, taylorVia σ (C.twistedTranslate 1 (x * Ω₀) C.θ) =
          taylorAtZero (D.twistedTranslate 1 (x * (Ω * b)) D.θ) := by
    obtain ⟨v, hv, h_translate⟩ := C.exists_taylorVia_twistedTranslate_theta D σ
      (C.galConjugate_a₁ σ) Ω₀ (by simp [h₀, mem_scaledIdeal, quadInt]) S
    obtain ⟨a, rfl⟩ := h_le v hv
    exact ⟨a / e, ⟨ι a, coe_mem_Ô a, by simp [ι, Algebra.smul_def, div_eq_inv_mul]⟩, hv,
      h_translate⟩
  choose b hb_compact hb_period hb using h_period
  obtain ⟨β, -, hβ⟩ : ∃ β ∈ (fun z ↦ (e : QuadField d)⁻¹ • z) '' Ô (QuadField d),
      MapClusterPt β .atTop (ι ∘ b) :=
    (isCompact_Ô.smul _).exists_mapClusterPt_of_frequently (.of_forall hb_compact)
  refine ⟨β, fun x ↦ ?_⟩
  -- Some `m ≠ 0` makes `m x` integral; take `U` so small that its points in `K` are congruent
  -- modulo `2 m e`.
  obtain ⟨m, hm_ne, hm⟩ : ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ ((m : QuadField d) * x) := by
    simpa [← algebraMap_mem_Ô] using exists_forall_mul_mem_Ô ![ι x]
  obtain ⟨U, hU, hU_int⟩ := exists_mem_nhds_isIntegral_sub_div (β * ι x)
    (show 2 * m * e ≠ 0 by positivity)
  refine ⟨U, hU, fun x' hx' ↦ ?_⟩
  have h_freq : ∃ᶠ S in .atTop, ι (b S) * ι x ∈ U :=
    hβ.frequently ((continuous_mul_const (ι x)).continuousAt.preimage_mem_nhds hU)
  obtain ⟨S, hS, hS_near⟩ := h_freq.forall_exists_of_atTop {x}
  have h_point : ((b S * x : QuadField d) : ℂ) * Ω = x * (Ω * b S) := by
    simp [mul_comm, mul_left_comm]
  have h_mem : ((m * x : QuadField d) : ℂ) * (Ω * b S) ∈ D.Λ :=
    D.mul_mem_of_quadInt ⟨⟨m * x, hm⟩, rfl⟩ (hb_period S)
  have h_torsion : (m : ℂ) * ((b S * x : QuadField d) * Ω) ∈ D.Λ := by
    rw [h_point]
    simpa [mul_assoc] using h_mem
  rw [D.twistedTranslate_theta_eq_of_isIntegral he hm_ne hΩ h_torsion
    (hU_int x' (b S * x) hx' (by rwa [map_mul])), h_point]
  exact hb S x (hS (mem_singleton_self x))

/-- Data for complex multiplication of theta functions of a CM lattice `C` of `K = ℚ(√-d)`, under
an automorphism `σ` of `ℂ` over `K`. The number `Ω` scales the lattice of the conjugate curve
`C.galConjugate σ`, and the finite adele `β` of `K` describes the action of `σ` on the translates
of `θ` by the points `x Ω₀` with `x ∈ K`. -/
structure CMLattice.IsComplexMultiplicationData (C : CMLattice d) (σ : Gal(ℂ/QuadField d))
    (Ω₀ Ω : ℂˣ) (β : 𝔸f (QuadField d)) : Prop where
  /-- The lattice of the conjugate curve has the area `|Ω|² √d / 2`. -/
  area_eq : (C.galConjugate σ).area = ‖Ω.val‖ ^ 2 * √d / 2
  /-- A positive integral multiple of `Ω` is a period of the conjugate curve. -/
  exists_mul_mem_latticeModule : ∃ e : ℕ+, Ω.val * e ∈ (C.galConjugate σ).latticeModule
  /-- For `x' ∈ K` close enough to `β x` in the finite adeles, `σ` takes the Taylor series of the
  translate of `θ` by `x Ω₀` to that of the translate by `x' Ω` of the theta function of the
  conjugate curve. -/
  taylorVia_twistedTranslate_theta (x : QuadField d) :
    ∃ U ∈ nhds (β * algebraMap (QuadField d) (𝔸f (QuadField d)) x),
      ∀ x' : QuadField d, algebraMap (QuadField d) (𝔸f (QuadField d)) x' ∈ U →
        taylorVia σ (C.twistedTranslate 1 (x * Ω₀) C.θ) =
          taylorAtZero ((C.galConjugate σ).twistedTranslate 1 (x' * Ω) (C.galConjugate σ).θ)

/-- Complex multiplication for theta functions, for `d` a prime `≡ 7 (mod 8)` and `K = ℚ(√-d)`. Let
the lattice of `C` be `Ω₀ 𝓞_K` and let `σ` be an automorphism of `ℂ` over `K`. There are a number
`Ω` and a finite adele `β` of `K` such that `C.IsComplexMultiplicationData σ Ω₀ Ω β` holds. This
means that the lattice of the conjugate curve `C.galConjugate σ` has the area `|Ω|² √d / 2` and
contains a multiple `Ω e`; and that for each `x ∈ K` and each `x' ∈ K` close enough to `β x` in
the finite adeles, `σ` takes the Taylor series of the translate of `θ` by `x Ω₀` to that of the
translate by `x' Ω` of the theta function of the conjugate curve. A case of the main theorem of
complex multiplication (Shimura, Introduction to the arithmetic theory of automorphic functions,
1971, Theorem 5.4), without the reciprocity law. -/
lemma CMLattice.complex_multiplication_theta (C : CMLattice d) (σ : Gal(ℂ/QuadField d)) {Ω₀ : ℂˣ}
    (h₀ : C.latticeModule = scaledIdeal d (Ω₀, 1)) :
    ∃ (Ω : ℂˣ) (β : 𝔸f (QuadField d)),
      C.IsComplexMultiplicationData σ Ω₀ Ω β := by
  -- The lattice of the conjugate curve `D` is `w 𝔠²`; with `n = N(𝔠)` take `Ω = w n` and `e = n`.
  let D : CMLattice d := C.galConjugate σ
  obtain ⟨w, ⟨𝔠, h𝔠⟩, hw : D.latticeModule =
      scaledIdeal d (w, FractionalIdeal.mk0 (QuadField d) ⟨𝔠, h𝔠⟩ ^ 2)⟩ :=
    D.exists_latticeModule_eq_scaledIdeal_sq
  have hn : 𝔠.absNorm ≠ 0 := Ideal.absNorm_ne_zero_of_nonZeroDivisors ⟨𝔠, h𝔠⟩
  let Ω : ℂˣ := w * Units.mk0 (𝔠.absNorm : ℂ) (mod_cast hn)
  have h_lattice (z : ℂ) :
      z ∈ D.Λ ↔ ∃ a ∈ 𝔠 ^ 2, Ω.val * ((a : QuadField d) / 𝔠.absNorm : QuadField d) = z := by
    have h_mem : z ∈ D.Λ ↔ ∃ a ∈ 𝔠 ^ 2, (w : ℂ) * (a : QuadField d) = z := by
      change z ∈ D.latticeModule ↔ _
      simp [hw, mem_scaledIdeal, ← coeIdeal_pow]
    simpa [Ω, mul_assoc, mul_div_cancel₀, hn] using h_mem
  have h_multiple : Ω.val * 𝔠.absNorm ∈ D.Λ :=
    (h_lattice _).2 ⟨_, Ideal.pow_mem_pow 𝔠.absNorm_mem 2, by simp [sq, hn]⟩
  have h_le (v : ℂ) (hv : v ∈ D.Λ) :
      ∃ a : 𝓞 (QuadField d), Ω.val * ((a : QuadField d) / 𝔠.absNorm : QuadField d) = v :=
    ((h_lattice v).1 hv).imp fun a ↦ And.right
  obtain ⟨β, hβ⟩ := C.exists_finAdele_taylorVia_twistedTranslate_theta σ h₀ hn h_multiple h_le
  -- The area of `w 𝔠²` is `|w|² N(𝔠)² √d / 2`.
  have h_area : D.area = ‖Ω.val‖ ^ 2 * √d / 2 := by
    simp [area_eq_of_eq_scaledIdeal hw, Ω, field, coeIdeal_absNorm]
  exact ⟨Ω, β,
    { area_eq := h_area
      exists_mul_mem_latticeModule := ⟨⟨𝔠.absNorm, Nat.pos_of_ne_zero hn⟩, h_multiple⟩
      taylorVia_twistedTranslate_theta := hβ }⟩

/-- Let `f` be a family of pairs (number, ideal) over the class group such that each
`scaledIdeal d (f c)`, the module `u 𝔞` for `f c = (u, 𝔞)`, multiplies the lattice of `A c` into
that of `B c`, and the product of the ideals contains `1`. Then the product of the numbers is
`p`-adically integral, for the place `ιₚ : ℂ → ℂ_p`. -/
lemma CMLattice.norm_prod_le_one {p : ℕ} [Fact p.Prime] [PadicPlace p]
    {f : ClassGroup (𝓞 (QuadField d)) →
      ℂˣ × (FractionalIdeal (nonZeroDivisors (𝓞 (QuadField d))) (QuadField d))ˣ}
    {A B : ClassGroup (𝓞 (QuadField d)) → CMLattice d}
    (hf : ∀ c : ClassGroup (𝓞 (QuadField d)),
      scaledIdeal d (f c) * (A c).latticeModule ≤ (B c).latticeModule)
    (h_one : 1 ∈ (∏ c : ClassGroup (𝓞 (QuadField d)), f c).2.val) :
    ‖ιₚ (∏ c : ClassGroup (𝓞 (QuadField d)), f c).1‖ ≤ 1 := by
  -- the integral elements form an `𝓞_K`-algebra `O`; it contains each factor because a number
  -- that maps one CM lattice into another is integral (`norm_le_one_of_mapsTo_lattice`)
  let O : Subalgebra (𝓞 (QuadField d)) ℂ :=
    ⟨(valRingCp p).toSubsemiring.comap ιₚ, norm_ringOfIntegers_le (ιₚ.domRestrict (QuadField d))⟩
  have h_factor (c : ClassGroup (𝓞 (QuadField d))) : scaledIdeal d (f c) ≤ O.toSubmodule :=
    fun a ha ↦ norm_le_one_of_mapsTo_lattice (A c) (Submodule.mul_le.mp (hf c) a ha)
  have h_prod : scaledIdeal d (∏ c, f c) ≤ O.toSubmodule :=
    calc _ = ∏ c, scaledIdeal d (f c) := map_prod ..
      _ ≤ O.toSubmodule ^ classNumber (QuadField d) :=
          prod_le_pow_card univ _ _ fun c _ ↦ h_factor c
      _ = O.toSubmodule := O.isIdempotentElem_toSubmodule.pow_eq (classNumber_ne_zero _)
  exact h_prod (mem_scaledIdeal.mpr ⟨1, h_one, by simp⟩)

omit [PrimeSevenModEight d] in
/-- `u⁻¹ 𝔞⁻¹ M' ⊆ M` if and only if `M' ⊆ u 𝔞 M`, for `𝓞_K`-submodules `M`, `M'` of `ℂ` and a pair
`x = (u, 𝔞)`, with `scaledIdeal d x = u 𝔞`. -/
lemma QuadField.scaledIdeal_inv_mul_le_iff
    (x : ℂˣ × (FractionalIdeal (nonZeroDivisors (𝓞 (QuadField d))) (QuadField d))ˣ)
    {M M' : Submodule (𝓞 (QuadField d)) ℂ} :
    scaledIdeal d x⁻¹ * M' ≤ M ↔ M' ≤ scaledIdeal d x * M :=
  Units.inv_mul_le_iff ((scaledIdeal d).toHomUnits x)

/-- Let `f c = (u c, 𝔞 c)` be a family over the class group such that the module
`scaledIdeal d (f c) = u c 𝔞 c` times the lattice of `A c` is the lattice of `B c`, and the product
of the ideals `𝔞 c` is `1`. Then the product of the absolute values of the `u c` at the `p`-adic
place `ιₚ : ℂ → ℂ_p` is `1`. -/
lemma CMLattice.prod_norm_eq_one {p : ℕ} [Fact p.Prime] [PadicPlace p]
    {f : ClassGroup (𝓞 (QuadField d)) →
      ℂˣ × (FractionalIdeal (nonZeroDivisors (𝓞 (QuadField d))) (QuadField d))ˣ}
    {A B : ClassGroup (𝓞 (QuadField d)) → CMLattice d}
    (hf : ∀ c : ClassGroup (𝓞 (QuadField d)),
      (B c).latticeModule = scaledIdeal d (f c) * (A c).latticeModule)
    (h_prod : ∏ c : ClassGroup (𝓞 (QuadField d)), (f c).2 = 1) :
    ∏ c : ClassGroup (𝓞 (QuadField d)), ‖ιₚ (f c).1‖ = 1 := by
  -- both the product and its inverse are integral (`norm_prod_le_one`)
  have h_le : ∏ c, ‖ιₚ (f c).1‖ ≤ 1 := by
    simpa [fst_prod] using norm_prod_le_one (fun c ↦ (hf c).ge) (by simp [snd_prod, h_prod])
  have h_inv : (∏ c, ‖ιₚ (f c).1‖)⁻¹ ≤ 1 := by
    simpa [fst_prod] using
      norm_prod_le_one (fun c ↦ (scaledIdeal_inv_mul_le_iff (f c)).2 (hf c).le)
        (by simp [snd_prod, h_prod])
  exact h_le.antisymm ((inv_le_one₀ (prod_pos (by simp))).1 h_inv)

/-- Let `d` be a prime `≡ 7 (mod 8)`. An automorphism `σ` of `ℂ` over `K = ℚ(√-d)` respects
isogenies: if `scaledIdeal d x = u 𝔞`, for `x = (u, 𝔞)`, multiplies the lattice of `C` into that of
`D`, then `σ(u) 𝔞` multiplies the lattice of `C.galConjugate σ` into that of `D.galConjugate σ`.
Here `C.galConjugate σ` is a chosen CM lattice whose number `a₁` is `σ a₁`, where `a₁` is the chosen
square root of `12 ℘(t)` at the point `t` of order two, with the lattice scaled so that
`℘''(t) = 2`. -/
lemma CMLattice.scaledIdeal_map_mul_galConjugate_le (σ : Gal(ℂ/QuadField d)) {C D : CMLattice d}
    {x : ℂˣ × (FractionalIdeal (nonZeroDivisors (𝓞 (QuadField d))) (QuadField d))ˣ}
    (h_le : scaledIdeal d x * C.latticeModule ≤ D.latticeModule) :
    scaledIdeal d (x.1.map σ, x.2) * (C.galConjugate σ).latticeModule ≤
      (D.galConjugate σ).latticeModule := by
  simp_rw [Submodule.mul_le, mem_scaledIdeal] at h_le ⊢
  rintro _ ⟨y, hy, rfl⟩ l hl
  obtain ⟨N, hN⟩ := exists_isIsogeny_of_mul_mem_lattice (h_le _ ⟨y, hy, rfl⟩)
  -- `using!` reads the membership in `latticeModule` as one in the lattice
  simpa [show σ (y : ℂ) = y from σ.commutes y] using!
    conj_isogeny_mul_mem_lattice σ (C.galConjugate_a₁ σ) (D.galConjugate_a₁ σ) hN hl

/-- If the lattice of `D` is `u 𝔞` times that of `C`, for `x = (u, 𝔞)`, then for `σ` an automorphism
of `ℂ` over `K` the lattice of `D.galConjugate σ` is `σ(u) 𝔞` times that of `C.galConjugate σ`. -/
lemma CMLattice.latticeModule_galConjugate_eq_mul (σ : Gal(ℂ/QuadField d)) {C D : CMLattice d}
    {x : ℂˣ × (FractionalIdeal (nonZeroDivisors (𝓞 (QuadField d))) (QuadField d))ˣ}
    (h_lattice : D.latticeModule = scaledIdeal d x * C.latticeModule) :
    (D.galConjugate σ).latticeModule =
      scaledIdeal d (x.1.map σ, x.2) * (C.galConjugate σ).latticeModule := by
  refine le_antisymm ?_ (scaledIdeal_map_mul_galConjugate_le σ h_lattice.ge)
  have h_inv : scaledIdeal d (x.1.map σ, x.2)⁻¹ * (D.galConjugate σ).latticeModule ≤
      (C.galConjugate σ).latticeModule :=
    (scaledIdeal_map_mul_galConjugate_le σ ((scaledIdeal_inv_mul_le_iff x).2 h_lattice.le) :)
  exact (scaledIdeal_inv_mul_le_iff _).1 h_inv

/-- There are fractional ideals of `K`, one in each ideal class, whose product is `(1)`. -/
lemma QuadField.exists_mk_eq_and_prod_eq_one :
    ∃ 𝔠 : ClassGroup (𝓞 (QuadField d)) →
        (FractionalIdeal (nonZeroDivisors (𝓞 (QuadField d))) (QuadField d))ˣ,
      (∀ 𝒞 : ClassGroup (𝓞 (QuadField d)), ClassGroup.mk (QuadField d) (𝔠 𝒞) = 𝒞) ∧
      ∏ 𝒞 : ClassGroup (𝓞 (QuadField d)), 𝔠 𝒞 = 1 := by
  -- Choose `𝔟 𝒞` in each class and put `𝔠 𝒞 = 𝔟 (𝒞²) / 𝔟 𝒞`; squaring permutes the classes.
  have h_rep : ∀ 𝒞 : ClassGroup (𝓞 (QuadField d)), ∃ 𝔟, ClassGroup.mk (QuadField d) 𝔟 = 𝒞 :=
    induction (QuadField d) fun 𝔟 ↦ ⟨𝔟, rfl⟩
  choose 𝔟 h𝔟 using h_rep
  refine ⟨fun 𝒞 ↦ 𝔟 (𝒞 ^ 2) / 𝔟 𝒞, fun 𝒞 ↦ by simp [h𝔟, sq], ?_⟩
  rw [prod_div_distrib, classGroup_sq_bijective.prod_comp 𝔟, div_self']

/-- Writing the lattice `u 𝔞` of a CM lattice `E` as `a (ℤ τ + ℤ)` expresses the image of `𝔞` in
`ℂ` as `(u⁻¹ a) (ℤ + ℤ τ)` and identifies `exp (6 · logPeriod τ)` with `(area / π)⁶ |a₁⁴ - 64|`. -/
private lemma CMLattice.exists_tau_image_and_exp_logPeriod {E : CMLattice d}
    {x : ℂˣ × (FractionalIdeal (nonZeroDivisors (𝓞 (QuadField d))) (QuadField d))ˣ}
    (hE : E.latticeModule = scaledIdeal d x) :
    ∃ τ : UpperHalfPlane,
      (∃ c : ℂ, c ≠ 0 ∧ (QuadField d).val.toRingHom '' (x.2.val : Set (QuadField d)) =
        (c * ·) '' (Submodule.span ℤ {(1 : ℂ), (τ : ℂ)} : Set ℂ)) ∧
      rexp (6 * τ.logPeriod) = (E.area / π) ^ 6 * ‖E.a₁ ^ 4 - 64‖ := by
  obtain ⟨a, τ, e, he, ha, h_area⟩ := exists_lattice_eq_mul_tau E.periodPair
  refine ⟨τ, ⟨(x.1 : ℂ)⁻¹ * a, mul_ne_zero (inv_ne_zero x.1.ne_zero) ha, ?_⟩, ?_⟩
  · -- `u y ∈ E.Λ = a (ℤ τ + ℤ)` if and only if `y ∈ (u⁻¹ a) (ℤ + ℤ τ)`.
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h_mem : (x.1 : ℂ) * (y : QuadField d) ∈ E.Λ := hE.ge (mem_scaledIdeal.2 ⟨y, hy, rfl⟩)
      let p : ℤ × ℤ := e.symm ⟨_, h_mem⟩
      have hp : (x.1 : ℂ) * (y : QuadField d) = a * (p.1 * τ + p.2) := by simpa [p] using he p
      refine ⟨p.1 * τ + p.2, Submodule.mem_span_pair.2 ⟨p.2, p.1, by simp [add_comm]⟩, ?_⟩
      dsimp only
      rw [mul_assoc, ← hp, inv_mul_cancel_left₀ x.1.ne_zero]
      rfl
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨n, m, rfl⟩ := Submodule.mem_span_pair.1 hw
      have h_mem : (x.1 : ℂ) * (((x.1 : ℂ)⁻¹ * a) * (n • (1 : ℂ) + m • (τ : ℂ))) ∈
          scaledIdeal d x := by
        rw [← hE, ← mul_assoc, mul_inv_cancel_left₀ x.1.ne_zero,
          show a * (n • (1 : ℂ) + m • (τ : ℂ)) = (e (m, n) : ℂ) by simp [he, add_comm]]
        exact (e (m, n)).property
      obtain ⟨y, hy, hy_eq⟩ := mem_scaledIdeal.1 h_mem
      exact ⟨y, hy, mul_left_cancel₀ x.1.ne_zero hy_eq⟩
  · -- With `a₁⁴ - 64 = (2 π / a)¹² η(τ)²⁴` and `area = |a|² Im τ`, compare sixth powers.
    have h_disc : ‖E.a₁ ^ 4 - 64‖ = (2 * π / ‖a‖) ^ 12 * ‖ModularForm.eta (τ : ℂ)‖ ^ 24 := by
      rw [← E.disc_eq, g₂_pow_three_sub_g₃_sq_eq_discriminant he, ModularForm.discriminant,
        norm_mul, norm_pow, norm_pow, norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg pi_nonneg]
    have h_pos_disc : 0 < ‖E.a₁ ^ 4 - 64‖ := by
      rw [← E.disc_eq]
      exact norm_pos_iff.2 (weierstrass_disc_ne_zero E.periodPair)
    have h_eta_pos : 0 < ‖ModularForm.eta (τ : ℂ)‖ :=
      (norm_nonneg _).lt_of_ne' fun h0 ↦ h_pos_disc.ne' (by simp [h_disc, h0])
    have h_inner_pos : 0 < 4 * π * τ.im * ‖ModularForm.eta (τ : ℂ)‖ ^ 4 := by
      have h_im_pos : 0 < τ.im := τ.im_pos
      positivity
    rw [show (6 : ℝ) * τ.logPeriod = (6 : ℕ) * τ.logPeriod by norm_num, Real.exp_natCast_mul,
      UpperHalfPlane.logPeriod_def, Real.exp_log h_inner_pos, h_area, h_disc]
    field [norm_ne_zero_iff.2 ha]

/-- The formula of Chowla and Selberg, with a unit: for a CM lattice `C` for `K = ℚ(√-d)` there is
a number `u`, a unit at every `p`-adic place `ιₚ : ℂ → ℂ_p`, such that for the automorphisms `σ` of
`ℂ` over `K` the lattices `σ(u) Λ^σ`, `Λ^σ` the lattice of `C.galConjugate σ`, all have the area
`π exp (γ - Re L'/L(1, χ_K)) 2π / √d`, where the exponent is `chowlaSelbergConst d`. -/
lemma CMLattice.chowla_selberg (C : CMLattice d) :
    ∃ u : ℂ,
      -- `u` has norm one at every `p`-adic place
      (∀ (p : ℕ) [Fact p.Prime] [PadicPlace p], ‖ιₚ u‖ = 1) ∧
      -- the area of every conjugate lattice
      ∀ σ : Gal(ℂ/QuadField d),
        (C.galConjugate σ).area * ‖σ u‖ ^ 2 = π * rexp (chowlaSelbergConst d) * (2 * π / √d) := by
  -- Take ideals `𝔠 𝒞`, one in each class, with product `(1)`, CM lattices `D 𝒞 = μ 𝒞 • 𝔠 𝒞 • Λ`,
  -- and a `12 h`-th root `u` of `∏ (μ 𝒞)¹² disc (D 𝒞)`, `h` the class number. Tau Ceti's
  -- `chowlaSelberg_classMean`, applied to the conjugates of the `D 𝒞`, gives the area.
  obtain ⟨𝔠, h_class : ∀ 𝒞, ClassGroup.mk (QuadField d) (𝔠 𝒞) = 𝒞, h_prod : ∏ 𝒞, 𝔠 𝒞 = 1⟩ :=
    exists_mk_eq_and_prod_eq_one (d := d)
  choose D μ hD using fun 𝒞 ↦ C.exists_latticeModule_eq_scaledIdeal_mul (𝔠 𝒞)
  have h_pos : 0 < 12 * classNumber (QuadField d) := by simp [classNumber_pos]
  obtain ⟨u, hu⟩ := exists_pow_nat_eq (∏ 𝒞, μ 𝒞 ^ 12 * ((D 𝒞).a₁ ^ 4 - 64) : ℂ) h_pos
  refine ⟨u, fun p _ _ ↦ ?_, fun σ ↦ ?_⟩
  · -- `∏ μ 𝒞` is a unit, and so are the discriminants (`norm_disc_eq_one`)
    rw [← pow_left_inj₀ (norm_nonneg _) zero_le_one h_pos.ne', ← norm_pow, ← map_pow, hu]
    simp [prod_mul_distrib, prod_pow, map_ofNat, norm_disc_eq_one,
      prod_norm_eq_one (A := fun _ ↦ C) hD h_prod]
  -- the conjugates `E 𝒞` of the `D 𝒞` lie one in each class
  let E (𝒞 : ClassGroup (𝓞 (QuadField d))) : CMLattice d := (D 𝒞).galConjugate σ
  obtain ⟨x, hx⟩ := (C.galConjugate σ).exists_latticeModule_eq_scaledIdeal
  have hE (𝒞 : ClassGroup (𝓞 (QuadField d))) :
      (E 𝒞).latticeModule = scaledIdeal d ((μ 𝒞).map σ * x.1, 𝔠 𝒞 * x.2) := by
    rw [latticeModule_galConjugate_eq_mul σ (hD 𝒞), hx, ← map_mul, Prod.mk_mul_mk]
  choose τ hτ_im hτ_exp using fun 𝒞 ↦ exists_tau_image_and_exp_logPeriod (hE 𝒞)
  let x₀ : ClassGroup (𝓞 (QuadField d)) := ClassGroup.mk (QuadField d) x.2
  have hd2 : d ≠ 2 := by
    have hd8 : d % 8 = 7 := PrimeSevenModEight.mod_eight
    omega
  have h_cs : (∑ g, (τ (g * x₀⁻¹)).logPeriod) / classNumber (QuadField d) =
      eulerMascheroniConstant + Real.log (2 * π / √(1 * d : ℕ)) -
        (deriv (quadTwist (N := 1) 1 d).LFunction 1 /
          (quadTwist (N := 1) 1 d).LFunction 1).re := by
    simpa [ofReal_re, sub_re] using congrArg Complex.re <|
      TauCeti.NumberField.chowlaSelberg_classMean (finrank_eq_two d) (QuadField d).val.toRingHom
        (1 * d) (by simpa using discr_eq_neg (d := d)) (quadTwist (N := 1) 1 d)
        (fun _ hs ↦ dedekindZeta_eq_riemannZeta_mul hs) (fun g ↦ τ (g * x₀⁻¹)) fun g ↦
          ⟨𝔠 (g * x₀⁻¹) * x.2, by simp [x₀, map_mul, h_class], hτ_im (g * x₀⁻¹)⟩
  have h_sum_shift : ∑ g, (τ (g * x₀⁻¹)).logPeriod = ∑ 𝒞, (τ 𝒞).logPeriod :=
    Fintype.sum_equiv (Equiv.mulRight x₀⁻¹) _ _ fun _ ↦ rfl
  have h_ent : entireL (quadTwist (N := 1) 1 d) = (quadTwist (N := 1) 1 d).LFunction :=
    ite_eq_right (quadTwist_ne_one 1 d hd2 (Nat.coprime_one_left d))
  have h_mean : (∑ 𝒞, (τ 𝒞).logPeriod) / classNumber (QuadField d) =
      chowlaSelbergConst d + Real.log (2 * π / √d) := by
    rw [h_sum_shift, Nat.cast_mul, Nat.cast_one, one_mul, ← logDeriv_apply, ← h_ent] at h_cs
    rw [h_cs, chowlaSelbergConst]
    ring
  -- compare `6 h`-th powers of `exp (mean)` and `((C.galConjugate σ).area * ‖σ u‖ ^ 2) / π`
  set A : ℝ := (C.galConjugate σ).area with hA
  set B : ℝ := A * ‖σ u‖ ^ 2
  have h_area (𝒞 : ClassGroup (𝓞 (QuadField d))) :
      (E 𝒞).area = ‖σ (μ 𝒞)‖ ^ 2 * absNorm (𝔠 𝒞).val * A := by
    simp [hA, area_eq_of_eq_scaledIdeal (hE 𝒞), area_eq_of_eq_scaledIdeal hx, field]
  have h_norm : ∏ 𝒞, (absNorm (𝔠 𝒞).val : ℝ) = 1 := by
    simp [← Rat.cast_prod, ← map_prod, ← Units.coe_prod, h_prod]
  have h_root : ‖σ u‖ ^ (12 * classNumber (QuadField d)) =
      ∏ 𝒞, ‖σ (μ 𝒞)‖ ^ 12 * ‖(E 𝒞).a₁ ^ 4 - 64‖ := by
    rw [← norm_pow, ← map_pow, hu]
    simp [E, galConjugate_a₁, map_ofNat]
  have h6h : 6 * classNumber (QuadField d) ≠ 0 := by simp [classNumber_ne_zero]
  have hB_nonneg : 0 ≤ B / π := div_nonneg (mul_nonneg (area_pos _).le (sq_nonneg _)) pi_pos.le
  have h_pow : rexp ((∑ 𝒞, (τ 𝒞).logPeriod) / classNumber (QuadField d)) ^
      (6 * classNumber (QuadField d)) = (B / π) ^ (6 * classNumber (QuadField d)) :=
    calc rexp ((∑ 𝒞, (τ 𝒞).logPeriod) / classNumber (QuadField d)) ^
          (6 * classNumber (QuadField d))
        = rexp (6 * ∑ 𝒞, (τ 𝒞).logPeriod) := by
          rw [← Real.exp_natCast_mul]
          congr 1
          push_cast
          field [Nat.cast_ne_zero.2 (classNumber_ne_zero (QuadField d))]
      _ = ∏ 𝒞, rexp (6 * (τ 𝒞).logPeriod) := by rw [mul_sum, Real.exp_sum]
      _ = ∏ 𝒞, (absNorm (𝔠 𝒞).val : ℝ) ^ 6 * (A / π) ^ 6 *
            (‖σ (μ 𝒞)‖ ^ 12 * ‖(E 𝒞).a₁ ^ 4 - 64‖) := by
          refine prod_congr rfl fun 𝒞 _ ↦ ?_
          rw [hτ_exp 𝒞, h_area 𝒞]
          ring
      _ = (B / π) ^ (6 * classNumber (QuadField d)) := by
          rw [prod_mul_distrib, prod_mul_distrib, prod_pow, h_norm, ← h_root]
          simp only [one_pow, one_mul, prod_const, Finset.card_univ, classNumber, B]
          rw [pow_mul ‖σ u‖ 12, pow_mul (A * ‖σ u‖ ^ 2 / π) 6, ← mul_pow]
          congr 1
          ring
  have h_eq : rexp ((∑ 𝒞, (τ 𝒞).logPeriod) / classNumber (QuadField d)) = B / π :=
    (pow_left_inj₀ (Real.exp_pos _).le hB_nonneg h6h).1 h_pow
  have hd_pos : 0 < d := NeZero.pos d
  rw [h_mean, Real.exp_add, Real.exp_log (by positivity)] at h_eq
  calc B = B / π * π := (div_mul_cancel₀ B pi_ne_zero).symm
    _ = π * rexp (chowlaSelbergConst d) * (2 * π / √d) := by
      rw [← h_eq]
      ring

end New
