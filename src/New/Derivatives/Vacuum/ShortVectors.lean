module

import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Data.Rat.Cast.OfScientific
public import New.Reduction.Data.AdmissibleData
import New.Reduction.Data.Magnitudes

/-!
# Tight frames in `𝔞₀`

A tight frame of length `h` is a finite family of vectors `y` of the lattice `𝔞₀`, counted with
multiplicities, such that `∑ y, (y† z) y = h z` for all `z`: a resolution of `h`.

* `New.Parameters.exists_isTightFrame_coprime`: a tight frame in `𝔞₀` of length `h ≤ (d q₁) ^ 6`
  prime to `q₁`, together with the unit-linear-form property.
* `New.Parameters.exists_isTightFrame_of_coprime`: this frame and the powers of `ζ` give tight
  frames of every length `m ≥ q₁ h + R (q₁ + h)` with multiplicities at least `R`.
* `New.Data.exists_isTightFrame`: a tight frame of length `p₀ p₁ = D.M` with large multiplicities,
  where `p₀` and `p₁` are the two primes `D.levelPrime 0` and `D.levelPrime 1` of the data.

The powers of `ζ` form a tight frame of length `q₁`. To construct a tight frame of coprime length
`h` without using a dual basis, we solve a quadratic congruence `n z² + z + 1 ≡ 0 (mod q₁)` where
`n = (d + 1) / 4 = β (1 - β)`, set `t = (1 - β) + n z`, and for each prime factor `ℓ ∣ q₁` with
`q₁ = ℓ r` and `r = ℓ^a M` (`ℓ ∤ M`), we form the family
`u(ℓ, j, k, i) = ζ^j (0^k a_ℓ^i + (t M / q₁) (a_ℓ^i - a_ℓ^k))` where `a_ℓ = ζ^r`.
Summing over `(ℓ, j, k, i)` gives a tight frame whose length `h` is bounded by `(d q₁) ^ 6` and
coprime to `q₁`.

Notions from other files:
* `P.E s` is the field `E = K(ζ)`, where `K = ℚ(√-d)` and `ζ = P.ζ s` is a primitive root of unity
  of order `q₁ = P.q₁ s = P.q₀ * towerDeg s`. `P.zetaInt s` is `ζ` as an element of `𝓞 E`.
* `P.Φ s` is the set of infinite places of `E`; `Φ τ` is the complex embedding of `E` chosen at `τ`.
* `finiteImage id y ∈ Ô E` says that `y` lies in the lattice `𝔞₀ = E ∩ α Ô`, where `α` is the idele
  of the Weil data and `Ô` is the ring of integral finite adeles.
* `P.periodFactor s` is a complex number; by `norm_iota_periodFactor` its absolute value at an
  embedding `ιₚ : ℂ →+* ℂ_[p]` is given by the idele `α`.
* `β = (1 + √-d) / 2` is `quadGen d` in `ℂ`, `QuadField.betaK d` in `𝓞 K` and `P.betaKInE s` in
  `𝓞 E`.
-/

@[expose] public section

open Polynomial Finset ComplexConjugate NumberField

namespace New

section Families

variable {E I J : Type} [Field E] [CMType E] [WeilData E] [Fintype I] [Fintype J]

/-- The disjoint union of a tight frame `w` with multiplicities `m` and frame bound `M` and a tight
frame `w'` with multiplicities `m'` and frame bound `M'` is a tight frame with frame bound `M + M'`.
This disjoint union is the family `Sum.elim w w'` with multiplicities `Sum.elim m m'`. -/
lemma IsTightFrame.sumElim {w : I → E} {w' : J → E} {m : I → ℕ} {m' : J → ℕ} {M M' : ℕ}
    (hw : IsTightFrame w m M) (hw' : IsTightFrame w' m' M') :
    IsTightFrame (Sum.elim w w') (Sum.elim m m') (M + M') := by
  refine ⟨Sum.forall.2 ⟨hw.finiteImage_mem, hw'.finiteImage_mem⟩, fun σ τ ↦ ?_⟩
  simp [Fintype.sum_sum_type, hw.sum_mul_conj, hw'.sum_mul_conj, ite_add_ite]

end Families

/-- Let `d` be a prime with `d ≡ 7 mod 8`. An element of `K = ℚ(√-d)` fixed by complex conjugation
is rational. -/
lemma QuadField.exists_algebraMap_eq_of_star_eq {d : ℕ} [PrimeSevenModEight d] {a : QuadField d}
    (ha : star a = a) : ∃ q : ℚ, algebraMap ℚ (QuadField d) q = a := by
  -- The maximal real subfield of the quadratic field `K` does not contain `√-d`, so it is `ℚ`.
  let R : IntermediateField ℚ (QuadField d) :=
    (maximalRealSubfield (QuadField d)).toIntermediateField (by simp)
  have h_mem {x : QuadField d} : x ∈ R ↔ star x = x := mem_maximalRealSubfield_iff_star_eq
  have h_prime : (Module.finrank ℚ (QuadField d)).Prime := by
    simp [QuadField.finrank_eq_two, Nat.prime_two]
  have h_sqrt : QuadField.sqrtNegD d ∉ R := by
    simp [h_mem, neg_eq_self, Subtype.ext_iff, NeZero.ne]
  rcases (IntermediateField.isSimpleOrder_of_finrank_prime ℚ (QuadField d) h_prime).eq_bot_or_eq_top
    R with h_bot | h_top
  · exact IntermediateField.mem_bot.1 (h_bot.le (h_mem.2 ha))
  · exact absurd (h_top.ge IntermediateField.mem_top) h_sqrt

/-- Let `d` be a prime with `d ≡ 7 mod 8`. If a complex number `z` lies in `quadInt d`, the ring of
integers of `K = ℚ(√-d)` as a subring of `ℂ`, and is real, then `z` is a rational integer. -/
lemma exists_eq_intCast_of_mem_quadInt_of_conj_eq {d : ℕ} [PrimeSevenModEight d] {z : ℂ}
    (hz : z ∈ quadInt d) (h_real : conj z = z) : ∃ n : ℤ, z = n := by
  obtain ⟨a, rfl⟩ : ∃ a : 𝓞 (QuadField d), ((a : QuadField d) : ℂ) = z := RingHom.mem_range.1 hz
  have ha_real : star (a : QuadField d) = a :=
    Subtype.ext ((QuadField.coe_star_eq_conj d a).trans h_real)
  obtain ⟨q, hq⟩ : ∃ q : ℚ, algebraMap ℚ (QuadField d) q = a :=
    QuadField.exists_algebraMap_eq_of_star_eq ha_real
  have h_int : IsIntegral ℤ q := by
    rw [← isIntegral_algebraMap_iff (B := QuadField d), hq]
    exact a.isIntegral_coe
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, algebraMap ℤ ℚ n = q :=
    IsIntegrallyClosed.algebraMap_eq_of_integral h_int
  exact ⟨n, by simp [← hq]⟩

namespace Parameters

variable {P : Parameters} {s : ℕ}

open scoped Classical in
/-- An element `y` of `E` lies in the lattice `𝔞₀`, that is `finiteImage id y ∈ Ô E`, if and only if
`relDifferentGen * y` is integral at the finite places dividing `betaKInE = (1 + √-d) / 2` and `y`
is integral at the other finite places. Here `relDifferentGen` generates the different of `E/K`. -/
lemma finiteImage_mem_iff {y : P.E s} :
    finiteImage id y ∈ Ô (P.E s) ↔
      ∀ w : FinPlace (P.E s), w.valuation (P.E s)
        ((if P.betaKInE s ∈ w.asIdeal then (P.relDifferentGen s : P.E s) else 1) * y) ≤ 1 := by
  refine mem_Ô.trans (forall_congr' fun w ↦ ?_)
  by_cases hw : P.betaKInE s ∈ w.asIdeal <;> simp [finiteImage, WeilData.α, α, hw]

/-- `Φ τ (betaKInE s) = quadGen P.d` for every infinite place `τ` of `E`. -/
private lemma phi_betaKInE (τ : P.Φ s) : Φ τ (P.betaKInE s : P.E s) = quadGen P.d := by
  rw [show (P.betaKInE s : P.E s) = algebraMap P.K (P.E s) (QuadField.betaK P.d) from rfl,
    P.phi_algebraMap s τ]
  rfl

/-- Let `ζ` be a primitive `N`-th root of unity in a characteristic-zero domain `R`, and let `ℓ`
be a prime factor of `N = ℓ * r`. Writing `r = ℓ ^ a * M` with `ℓ ∤ M`, we have `M ≤ N`, the prime
factors of `N` dividing `M` are precisely those different from `ℓ`, and there exists `V ∈ R` with
`V ∣ M` and `Φ_N'(ζ) * (ζ ^ r - 1) * M = N * V`. -/
lemma exists_cyclotomic_different_factor {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {N : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ N) (ℓ : N.primeFactors) :
    ∃ r M : ℕ, M ≤ N ∧ N = ℓ.val * r ∧ (∀ p ∈ N.primeFactors, p ∣ M ↔ p ≠ ℓ.val) ∧
      ∃ V : R, V ∣ (M : R) ∧
        (cyclotomic N R).derivative.eval ζ * (ζ ^ r - 1) * M = N * V := by
  rcases ℓ with ⟨l, hl⟩
  obtain ⟨hl_prime, ⟨r, hN_eq⟩, hN_ne⟩ := Nat.mem_primeFactors.1 hl
  have hN_pos : 0 < N := Nat.pos_of_ne_zero hN_ne
  have hr_pos : 0 < r := Nat.pos_of_ne_zero fun hr0 ↦ hN_ne (by simp [hN_eq, hr0])
  have hr_lt : r < N := by
    rw [hN_eq]
    exact lt_mul_of_one_lt_left hr_pos hl_prime.one_lt
  obtain ⟨q, hq⟩ : (X ^ r - 1) * cyclotomic N R ∣ X ^ N - 1 :=
    X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd R
      (Nat.mem_properDivisors.2 ⟨⟨l, by rw [hN_eq, mul_comm]⟩, hr_lt⟩)
  obtain ⟨a, M, hl_ndvd_M, hr_eq⟩ := r.exists_eq_pow_mul_and_not_dvd hr_pos.ne' l hl_prime.ne_one
  have hM_le : M ≤ N := by
    calc M ≤ l ^ a * M := Nat.le_mul_of_pos_left M (pow_pos hl_prime.pos a)
      _ = r := hr_eq.symm
      _ ≤ N := hr_lt.le
  have hM_primes (p : ℕ) (hp : p ∈ N.primeFactors) : p ∣ M ↔ p ≠ l := by
    grind [Nat.Prime.dvd_mul, Nat.prime_eq_prime_of_dvd_pow, Nat.prime_dvd_prime_iff_eq]
  -- Differentiate `X ^ N - 1 = (X ^ r - 1) * Φ_N(X) * q(X)` at `ζ` and multiply by `ζ`.
  have h_root : (cyclotomic N R).eval ζ = 0 := hζ.isRoot_cyclotomic hN_pos
  have h_deriv_N :
      (N : R) = (ζ ^ r - 1) * (cyclotomic N R).derivative.eval ζ * (q.eval ζ * ζ) := by
    have h_eq := congrArg (fun f : R[X] ↦ f.derivative.eval ζ) hq
    simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul, eval_mul,
      eval_add, eval_sub, eval_pow, eval_X, eval_one, eval_C, h_root, zero_mul, mul_zero,
      zero_add] at h_eq
    have h_pow : ζ ^ (N - 1) * ζ = 1 := by
      rw [pow_sub_one_mul hN_ne, hζ.pow_eq_one]
    linear_combination ζ * h_eq - (N : R) * h_pow
  -- Expand `Φ_M(X ^ l) = Φ_{M l}(X) * Φ_M(X)` by `l ^ a` and differentiate at `ζ`.
  have hN_fac : M * l * l ^ a = N := by rw [hN_eq, hr_eq]; ring
  have h_exp_eq : expand R (l ^ a * l) (cyclotomic M R) =
      cyclotomic N R * expand R (l ^ a) (cyclotomic M R) := by
    have h_step :=
      congrArg (expand R (l ^ a)) (cyclotomic_expand_eq_cyclotomic_mul hl_prime hl_ndvd_M R)
    rw [expand_mul, h_step, map_mul, expand_pow_cyclotomic hl_prime (dvd_mul_left l M), hN_fac]
  have h_dvd_N : (N : R) ∣ (cyclotomic N R).derivative.eval ζ * (ζ ^ r - 1) * M := by
    have h_eq := congrArg (fun f : R[X] ↦ (M : R) * f.derivative.eval ζ) h_exp_eq
    simp only [derivative_expand, derivative_mul, eval_mul, eval_add, eval_natCast, eval_pow,
      eval_X, expand_eval, h_root, zero_mul, add_zero] at h_eq
    have hN_cast : (M : R) * ((l ^ a * l : ℕ) : R) = N := by
      have h_mul : M * (l ^ a * l) = N := by
        rw [← hN_fac]
        ring
      exact_mod_cast h_mul
    have h_step : (N : R) ∣ (M : R) * ((cyclotomic N R).derivative.eval ζ *
        (cyclotomic M R).eval (ζ ^ l ^ a)) :=
      ⟨(cyclotomic M R).derivative.eval (ζ ^ (l ^ a * l)) * ζ ^ (l ^ a * l - 1), by
        linear_combination -h_eq + (cyclotomic M R).derivative.eval (ζ ^ (l ^ a * l)) *
          ζ ^ (l ^ a * l - 1) * hN_cast⟩
    have h_eval : (cyclotomic M R).eval (ζ ^ l ^ a) ∣ ζ ^ r - 1 := by
      simpa [← pow_mul, ← hr_eq] using
        eval_dvd (x := ζ ^ l ^ a) (cyclotomic.dvd_X_pow_sub_one M R)
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      h_step.trans (mul_dvd_mul_left (M : R) (mul_dvd_mul_left _ h_eval))
  obtain ⟨V, hV_eq⟩ := h_dvd_N
  have hV_dvd_M : V ∣ (M : R) := by
    refine ⟨q.eval ζ * ζ, mul_left_cancel₀ (Nat.cast_ne_zero.2 hN_ne) ?_⟩
    linear_combination (q.eval ζ * ζ) * hV_eq + (M : R) * h_deriv_N
  exact ⟨r, M, hM_le, hN_eq, hM_primes, V, hV_dvd_M, hV_eq⟩

/-- Every prime factor of `q₁ = P.q₁ s` divides `n = (d + 1) / 4`, so `q₁ ∣ n ^ q₁`. -/
private lemma q₁_dvd_pow_q₁ : P.q₁ s ∣ ((P.d + 1) / 4) ^ P.q₁ s := by
  refine (Nat.dvd_iff_prime_pow_dvd_dvd _ _).2 fun p k hp h_dvd ↦ ?_
  obtain rfl | hk_pos := k.eq_zero_or_pos
  · exact one_dvd _
  have hk_le : k ≤ P.q₁ s :=
    (Nat.lt_pow_self hp.one_lt).le.trans (Nat.le_of_dvd (NeZero.pos _) h_dvd)
  exact pow_dvd_pow_of_dvd_of_le
    (P.dvd_d_add_one_div_four_of_dvd_q₁ hp ((dvd_pow_self p hk_pos.ne').trans h_dvd)) hk_le

/-- Since `n = (d + 1) / 4` is nilpotent modulo `q₁`, the quadratic polynomial `n y² + y + 1` has
a root `z < q₁` modulo `q₁`. -/
private lemma exists_quad_congr_mod_q₁ :
    ∃ z < P.q₁ s, ∃ e : ℕ, ((P.d + 1) / 4) * z ^ 2 + z + 1 = P.q₁ s * e := by
  set N : ℕ := P.q₁ s
  set n : ℕ := (P.d + 1) / 4
  -- The map `y ↦ n * y ^ 2 + y` on `ZMod N` is injective because `1 + n * (a + b)` is a unit.
  have h_inj : Function.Injective fun y : ZMod N ↦ (n : ZMod N) * y ^ 2 + y := by
    intro a b hab
    have h_nilp : IsNilpotent ((n : ZMod N) * (a + b)) :=
      ⟨N, by rw [mul_pow, ← Nat.cast_pow, (ZMod.natCast_eq_zero_iff _ N).2 q₁_dvd_pow_q₁, zero_mul]⟩
    have h_unit : IsUnit ((n : ZMod N) * (a + b) + 1) := h_nilp.isUnit_add_one
    have h_fac : ((n : ZMod N) * (a + b) + 1) * (a - b) = 0 := by linear_combination hab
    exact sub_eq_zero.1 (h_unit.mul_left_cancel (by simpa using h_fac))
  obtain ⟨y, hy⟩ := Finite.surjective_of_injective h_inj (-1 : ZMod N)
  have h_dvd : N ∣ n * y.val ^ 2 + y.val + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    linear_combination hy
  obtain ⟨e, he⟩ := h_dvd
  exact ⟨y.val, y.val_lt, e, he⟩

/-- Cyclotomic-orbit vector `ζ ^ j * (0 ^ k * a ^ i + (t * M / N) * (a ^ i - a ^ k))` in `P.E s`. -/
private noncomputable def orbitVec (N : ℕ) (t a : 𝓞 (P.E s)) (M j k i : ℕ) : P.E s :=
  (P.zetaInt s : P.E s) ^ j * ((0 : P.E s) ^ k * (a : P.E s) ^ i +
    ((t : P.E s) * (M : P.E s) / (N : P.E s)) * ((a : P.E s) ^ i - (a : P.E s) ^ k))

/-- If `N ∣ y * t * (M * (a - 1))` in `𝓞 E`, then `y * orbitVec N t a M j k i` has valuation at
most `1` at `v`. -/
private lemma valuation_mul_orbitVec_le_one (v : FinPlace (P.E s)) {N : ℕ} (hN : N ≠ 0)
    {y t a : 𝓞 (P.E s)} {M : ℕ} (j k i : ℕ) (hdvd : (N : 𝓞 (P.E s)) ∣ y * t * (M * (a - 1))) :
    v.valuation (P.E s) ((y : P.E s) * orbitVec N t a M j k i) ≤ 1 := by
  obtain ⟨q, hq⟩ := hdvd
  obtain ⟨g, hg⟩ : a - 1 ∣ a ^ i - a ^ k := by
    simpa using dvd_sub (sub_one_dvd_pow_sub_one a i) (sub_one_dvd_pow_sub_one a k)
  have h_eq : (y : P.E s) * orbitVec N t a M j k i =
      ((P.zetaInt s ^ j * (y * (0 : 𝓞 (P.E s)) ^ k * a ^ i + q * g) : 𝓞 (P.E s)) : P.E s) := by
    have hN_E : (N : P.E s) ≠ 0 := Nat.cast_ne_zero.2 hN
    have hg_E : (a : P.E s) ^ i - (a : P.E s) ^ k = ((a : P.E s) - 1) * (g : P.E s) := by
      exact_mod_cast hg
    have hq_E : (y : P.E s) * (t : P.E s) * ((M : P.E s) * ((a : P.E s) - 1)) =
        (N : P.E s) * (q : P.E s) := by
      exact_mod_cast hq
    simp only [orbitVec]
    rw [hg_E]
    field_simp [hN_E]
    push_cast
    linear_combination (P.zetaInt s : P.E s) ^ j * (g : P.E s) * hq_E
  rw [h_eq]
  exact v.valuation_le_one _

/-- If `n * z² + z + 1 = q₁ * e` for `n = (d + 1) / 4`, then `q₁` divides
`β ^ q₁ * (1 - β + n * z)` in `𝓞 E`, where `β = betaKInE`. -/
private lemma q₁_dvd_betaKInE_pow_mul {z e : ℕ}
    (he : ((P.d + 1) / 4) * z ^ 2 + z + 1 = P.q₁ s * e) :
    (P.q₁ s : 𝓞 (P.E s)) ∣
      P.betaKInE s ^ P.q₁ s * (1 - P.betaKInE s + (((P.d + 1) / 4 : ℕ) : 𝓞 (P.E s)) * z) := by
  let N : ℕ := P.q₁ s
  let n : 𝓞 (P.E s) := ((P.d + 1) / 4 : ℕ)
  let t : 𝓞 (P.E s) := 1 - P.betaKInE s + n * (z : 𝓞 (P.E s))
  obtain ⟨f, hf⟩ : N ∣ ((P.d + 1) / 4) ^ N := q₁_dvd_pow_q₁
  obtain ⟨w, hw⟩ := sub_dvd_pow_sub_pow (P.betaKInE s) (-n * (z : 𝓞 (P.E s))) N
  have hβ : P.betaKInE s * (1 - P.betaKInE s) = n := P.betaKInE_mul_one_sub s
  have h_prod : (P.betaKInE s - (-n * (z : 𝓞 (P.E s)))) * t = n * ((N : 𝓞 (P.E s)) * e) := by
    have he_O : n * (z : 𝓞 (P.E s)) ^ 2 + (z : 𝓞 (P.E s)) + 1 = (N : 𝓞 (P.E s)) * e := by
      dsimp only [N, n]
      exact_mod_cast he
    linear_combination hβ + n * he_O
  have hf_O : n ^ N = (N : 𝓞 (P.E s)) * f := by
    dsimp only [N, n]
    exact_mod_cast hf
  have h_pow_neg : (-n * (z : 𝓞 (P.E s))) ^ N = n ^ N * (-(z : 𝓞 (P.E s))) ^ N := by
    rw [show -n * (z : 𝓞 (P.E s)) = n * -(z : 𝓞 (P.E s)) by ring, mul_pow]
  refine ⟨n * e * w + f * (-(z : 𝓞 (P.E s))) ^ N * t, ?_⟩
  linear_combination t * hw + w * h_prod + (-(z : 𝓞 (P.E s))) ^ N * t * hf_O + t * h_pow_neg

/-- Inner sum identity for the cyclotomic-orbit tight frame: for `α, β', W : ℂ` with
`∑ i : Fin l, α ^ i = 0` and `∑ i : Fin l, β' ^ i = 0` (`0 < l`), summing
`(0 ^ k * α ^ i + W * (α ^ i - α ^ k)) * (0 ^ k * β' ^ i + conj W * (β' ^ i - β' ^ k))`
over `k, i : Fin l` yields `(1 + W + conj W + 2 * l * (W * conj W)) * ∑ i : Fin l, (α * β') ^ i`. -/
private lemma sum_inner_frame {l : ℕ} (hl : 0 < l) {α β' W : ℂ}
    (hα : ∑ i : Fin l, α ^ i.val = 0) (hβ' : ∑ i : Fin l, β' ^ i.val = 0) :
    ∑ k : Fin l, ∑ i : Fin l,
      ((0 : ℂ) ^ k.val * α ^ i.val + W * (α ^ i.val - α ^ k.val)) *
        ((0 : ℂ) ^ k.val * β' ^ i.val + conj W * (β' ^ i.val - β' ^ k.val)) =
      (1 + W + conj W + 2 * (l : ℂ) * (W * conj W)) * ∑ i : Fin l, (α * β') ^ i.val := by
  have : NeZero l := ⟨hl.ne'⟩
  -- Expand each summand into a `0 ^ k` term and a `W * conj W` term.
  have h_expand (k i : Fin l) :
      ((0 : ℂ) ^ k.val * α ^ i.val + W * (α ^ i.val - α ^ k.val)) *
        ((0 : ℂ) ^ k.val * β' ^ i.val + conj W * (β' ^ i.val - β' ^ k.val)) =
      ((if k = 0 then 1 + W + conj W else 0) + W * conj W) * (α * β') ^ i.val -
        ((0 : ℂ) ^ k.val + W) * conj W * β' ^ k.val * α ^ i.val -
        ((0 : ℂ) ^ k.val + conj W) * W * α ^ k.val * β' ^ i.val +
        W * conj W * (α * β') ^ k.val := by
    simp only [zero_pow_eq, Fin.val_eq_zero_iff, mul_pow]
    split_ifs <;> ring
  simp only [h_expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, hα, hβ', mul_zero, sub_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

/-- The Gram sum of the `ℓ`-th prime block of `orbitVec` over `(j, k, i) : Fin r × Fin ℓ × Fin ℓ`
equals `q₁ + M * (1 + 2 * n * (z + ℓ * (M * e)))` when `σ = τ` and `0` otherwise, where
`n = (d + 1) / 4` and `t = 1 - β + n * z`. -/
private lemma sum_orbitVec_mul_conj {z e : ℕ}
    (he_eq : ((P.d + 1) / 4) * z ^ 2 + z + 1 = P.q₁ s * e)
    (ℓ : (P.q₁ s).primeFactors) {r M : ℕ} (hN_eq : P.q₁ s = ℓ.val * r) (σ τ : P.Φ s) :
    ∑ j : Fin r, ∑ k : Fin ℓ.val, ∑ i : Fin ℓ.val,
      Φ σ (orbitVec (P.q₁ s) (1 - P.betaKInE s + (((P.d + 1) / 4 : ℕ) : 𝓞 (P.E s)) * z)
        (P.zetaInt s ^ r) M j.val k.val i.val) *
      conj (Φ τ (orbitVec (P.q₁ s) (1 - P.betaKInE s + (((P.d + 1) / 4 : ℕ) : 𝓞 (P.E s)) * z)
        (P.zetaInt s ^ r) M j.val k.val i.val)) =
      if σ = τ then
        ((P.q₁ s + M * (1 + 2 * ((P.d + 1) / 4) * (z + ℓ.val * (M * e))) : ℕ) : ℂ) else 0 := by
  let N : ℕ := P.q₁ s
  let n : ℕ := (P.d + 1) / 4
  let a : 𝓞 (P.E s) := P.zetaInt s ^ r
  have hℓ_prime : ℓ.val.Prime := Nat.prime_of_mem_primeFactors ℓ.property
  have h_prim_a : IsPrimitiveRoot a ℓ.val :=
    isPrimitiveRoot_zetaInt.pow (NeZero.pos N) (hN_eq.trans (mul_comm _ _))
  have h_sum_a : ∑ i : Fin ℓ.val, (a : P.E s) ^ i.val = 0 := by
    have h0 : ∑ i ∈ range ℓ.val, a ^ i = 0 := h_prim_a.geom_sum_eq_zero hℓ_prime.one_lt
    rw [← Fin.sum_univ_eq_sum_range] at h0
    exact_mod_cast h0
  let γ : ℂ := Φ σ (P.zetaInt s : P.E s) * conj (Φ τ (P.zetaInt s : P.E s))
  have hN_C : (P.q₀ : ℂ) * towerDeg s = N := by exact_mod_cast rfl
  have h_prod_sum : (∑ j : Fin r, γ ^ j.val) * (∑ i : Fin ℓ.val, (γ ^ r) ^ i.val) =
      if σ = τ then (N : ℂ) else 0 := by
    let eN : Fin ℓ.val × Fin r ≃ Fin N := finProdFinEquiv.trans (finCongr hN_eq.symm)
    have h_bij :
        (∑ p : Fin ℓ.val × Fin r, (γ ^ r) ^ p.fst.val * γ ^ p.snd.val) =
          ∑ m : Fin N, γ ^ m.val := by
      rw [← eN.sum_comp]
      refine Finset.sum_congr rfl fun ⟨i, j⟩ _ ↦ ?_
      simp [eN, finProdFinEquiv, pow_add, pow_mul]
      ring
    rw [mul_comm, Finset.sum_mul_sum, ← Fintype.sum_prod_type', h_bij]
    simpa [γ, mul_pow, map_pow, hN_C] using (P.isTightFrame_zeta_pow s 1).sum_mul_conj σ τ
  let tC : ℂ := 1 - quadGen P.d + (n : ℂ) * z
  let W : ℂ := tC * (M : ℂ) / (N : ℂ)
  have h_inner := sum_inner_frame (W := W) hℓ_prime.pos
    (by simpa [map_sum, map_pow] using congrArg (Φ σ) h_sum_a)
    (by simpa [map_sum, map_pow] using congrArg (conj ∘ Φ τ) h_sum_a)
  have h_u_term (j : Fin r) (k i : Fin ℓ.val) :
      Φ σ (orbitVec (P.q₁ s) (1 - P.betaKInE s + (((P.d + 1) / 4 : ℕ) : 𝓞 (P.E s)) * z)
        (P.zetaInt s ^ r) M j.val k.val i.val) *
      conj (Φ τ (orbitVec (P.q₁ s) (1 - P.betaKInE s + (((P.d + 1) / 4 : ℕ) : 𝓞 (P.E s)) * z)
        (P.zetaInt s ^ r) M j.val k.val i.val)) =
        γ ^ j.val *
          (((0 : ℂ) ^ k.val * Φ σ a ^ i.val + W * (Φ σ a ^ i.val - Φ σ a ^ k.val)) *
          ((0 : ℂ) ^ k.val * conj (Φ τ a) ^ i.val +
            conj W * (conj (Φ τ a) ^ i.val - conj (Φ τ a) ^ k.val))) := by
    simp only [orbitVec, map_mul, map_add, map_sub, map_div₀, map_pow, map_one, map_zero,
      map_natCast, phi_betaKInE, W, tC, γ, mul_pow, a, N, n]
    ring
  have h_αβ : Φ σ (a : P.E s) * conj (Φ τ (a : P.E s)) = γ ^ r := by
    simp [a, γ, mul_pow, map_pow]
  simp_rw [h_u_term, ← Finset.mul_sum, h_inner, h_αβ, ← Finset.sum_mul]
  rw [mul_left_comm, h_prod_sum]
  split_ifs
  · have hβ_sum : quadGen P.d + conj (quadGen P.d) = 1 := by
      have h_st := congrArg (fun x : 𝓞 (P.E s) ↦ Φ σ (x : P.E s)) (P.star_betaKInE s)
      simp only [coe_star_ringOfIntegers, map_star_complex, Complex.star_def, map_sub, map_one,
        phi_betaKInE] at h_st
      linear_combination h_st
    have h_t_add : tC + conj tC = 1 + 2 * (n : ℂ) * (z : ℂ) := by
      simp only [tC, map_add, map_sub, map_one, map_mul, map_natCast]
      linear_combination -hβ_sum
    have h_t_mul : tC * conj tC = (n : ℂ) * ((N : ℂ) * (e : ℂ)) := by
      have hβ_prod : quadGen P.d * (1 - quadGen P.d) = (n : ℂ) := by
        have hβ_mul : P.betaKInE s * (1 - P.betaKInE s) = (n : 𝓞 (P.E s)) :=
          P.betaKInE_mul_one_sub s
        simpa [phi_betaKInE] using congrArg (fun x : 𝓞 (P.E s) ↦ Φ σ (x : P.E s)) hβ_mul
      have he_C : (n : ℂ) * (z : ℂ) ^ 2 + (z : ℂ) + 1 = (N : ℂ) * (e : ℂ) := by
        dsimp only [N, n]
        exact_mod_cast he_eq
      simp only [tC, map_add, map_sub, map_one, map_mul, map_natCast]
      linear_combination tC * (-hβ_sum) + hβ_prod + (n : ℂ) * he_C
    have hW_conj : conj W = conj tC * (M : ℂ) / (N : ℂ) := by simp [W]
    rw [hW_conj]
    simp only [W]
    field_simp [Nat.cast_ne_zero.2 (NeZero.ne N)]
    push_cast
    rw [hN_C]
    linear_combination (M : ℂ) * (N : ℂ) * h_t_add + 2 * (ℓ.val : ℂ) * (M : ℂ) ^ 2 * h_t_mul
  · exact mul_zero _

/-- Elementary polynomial bound showing the sum of the prime-block lengths
`N + M ℓ * (1 + 2 * n * (z + ℓ * (M ℓ * e)))` over `ℓ ∈ N.primeFactors` is at most
`(d * N) ^ 6`. -/
private lemma sum_orbit_length_le {N z e : ℕ} (hN_pos : 0 < N) (hz : z < N)
    (he : ((P.d + 1) / 4) * z ^ 2 + z + 1 = N * e) {M : N.primeFactors → ℕ} (hM : ∀ ℓ, M ℓ ≤ N) :
    (∑ ℓ : N.primeFactors,
      (N + M ℓ * (1 + 2 * ((P.d + 1) / 4) * (z + ℓ.val * (M ℓ * e))))) ≤ (P.d * N) ^ 6 := by
  set n := (P.d + 1) / 4
  have hd_ge : 7 ≤ P.d := by
    have hmod : P.d % 8 = 7 := PrimeSevenModEight.mod_eight
    omega
  have he_le : e ≤ P.d * N := by
    have hNe : N * e ≤ N * (P.d * N) := by
      rw [show N * (P.d * N) = P.d * N ^ 2 by ring]
      linarith [Nat.mul_le_mul_left n (Nat.pow_le_pow_left hz.le 2),
        Nat.mul_le_mul_right (N ^ 2) (show n + 1 ≤ P.d by omega),
        Nat.le_self_pow (n := 2) (by decide) N]
    exact Nat.le_of_mul_le_mul_left hNe hN_pos
  have h_coeff : 2 + P.d + P.d ^ 2 ≤ P.d ^ 6 := by
    have hd_pos : 0 < P.d := by omega
    have h_d_le_sq : P.d ≤ P.d ^ 2 := Nat.le_self_pow (by norm_num) P.d
    have h_sq_cube : P.d ^ 2 * 7 ≤ P.d ^ 3 := by
      calc P.d ^ 2 * 7 ≤ P.d ^ 2 * P.d := Nat.mul_le_mul_left (P.d ^ 2) hd_ge
        _ = P.d ^ 3 := by ring
    have h_cube : 2 + P.d + P.d ^ 2 ≤ P.d ^ 3 := by omega
    exact h_cube.trans (Nat.pow_le_pow_right hd_pos (by norm_num))
  have h_term (ℓ : N.primeFactors) :
      N + M ℓ * (1 + 2 * n * (z + ℓ.val * (M ℓ * e))) ≤ P.d ^ 6 * N ^ 5 := by
    grw [hM ℓ, Nat.le_of_mem_primeFactors ℓ.property, hz.le, he_le, (show 2 * n ≤ P.d by omega)]
    calc N + N * (1 + P.d * (N + N * (N * (P.d * N))))
        = 2 * N ^ 1 + P.d * N ^ 2 + P.d ^ 2 * N ^ 4 := by ring
      _ ≤ (2 + P.d + P.d ^ 2) * N ^ 5 := by
          rw [add_mul, add_mul]
          gcongr <;> decide
      _ ≤ P.d ^ 6 * N ^ 5 := Nat.mul_le_mul_right _ h_coeff
  have h_card : Fintype.card N.primeFactors ≤ N := by
    rw [Fintype.card_coe]
    exact (Finset.card_le_card fun p hp ↦ Finset.mem_Icc.2
      ⟨(Nat.prime_of_mem_primeFactors hp).pos, Nat.le_of_mem_primeFactors hp⟩).trans_eq (by simp)
  calc _ ≤ ∑ _ℓ : N.primeFactors, P.d ^ 6 * N ^ 5 := Finset.sum_le_sum fun ℓ _ ↦ h_term ℓ
    _ ≤ N * (P.d ^ 6 * N ^ 5) := by simpa using Nat.mul_le_mul_right _ h_card
    _ = (P.d * N) ^ 6 := by ring

/-- `periodFactor * conj (Φ τ y)` has absolute value 1 at the embedding `ιₚ : ℂ →+* ℂ_[p]` (the
instance `PadicPlace p`) for all `τ` in the CM type. These numbers are the coefficients of the
linear form `z ↦ periodFactor * ∑ τ, conj (Φ τ y) * Φ τ z`. -/
def HasUnitLinearForm (P : Parameters) (s p : ℕ) [Fact p.Prime] [PadicPlace p] (y : P.E s) :
    Prop :=
  ∀ τ : InfinitePlace (P.E s), ‖(ιₚ (P.periodFactor s * conj (Φ τ y)) : ℂ_[p])‖ = 1

/-- There is a tight frame `v` in `𝔞₀` with multiplicities `1` of length `h ≤ (d q₁) ^ 6` prime to
`q₁`, such that for every prime `p` and embedding `ιₚ : ℂ →+* ℂ_[p]`, either `1` or some member
`v i` has `HasUnitLinearForm`. -/
theorem exists_isTightFrame_coprime (P : Parameters) (s : ℕ) :
    ∃ (h : ℕ) (I : Type) (_ : Fintype I) (v : I → P.E s),
      IsTightFrame v 1 h ∧
      h ≤ (P.d * P.q₁ s) ^ 6 ∧
      h.Coprime (P.q₁ s) ∧
      ∀ (p : ℕ) [Fact p.Prime] [PadicPlace p],
        P.HasUnitLinearForm s p 1 ∨ ∃ i : I, P.HasUnitLinearForm s p (v i) := by
  classical
  set N : ℕ := P.q₁ s
  set n : ℕ := (P.d + 1) / 4
  have hN_ne : N ≠ 0 := NeZero.ne N
  have hζ : IsPrimitiveRoot (P.zetaInt s) N := isPrimitiveRoot_zetaInt
  -- Factor `Φ_N'(ζ)` at each prime `ℓ ∣ N`, and solve `n z² + z + 1 = N e`.
  choose r M hM_le hN_eq hM_primes V hV_dvd hV_eq using
    fun ℓ : N.primeFactors ↦ exists_cyclotomic_different_factor hζ ℓ
  obtain ⟨z, hz_lt, e, he_eq⟩ := exists_quad_congr_mod_q₁ (P := P) (s := s)
  let t : 𝓞 (P.E s) := 1 - P.betaKInE s + (n : 𝓞 (P.E s)) * (z : 𝓞 (P.E s))
  let a (ℓ : N.primeFactors) : 𝓞 (P.E s) := P.zetaInt s ^ r ℓ
  -- The frame vectors indexed by `(ℓ, j, k, i) ∈ Σ ℓ : N.primeFactors, Fin (r ℓ) × Fin ℓ × Fin ℓ`.
  let I : Type := Σ ℓ : N.primeFactors, Fin (r ℓ) × Fin ℓ.val × Fin ℓ.val
  let u : I → P.E s := fun ⟨ℓ, j, k, i⟩ ↦ orbitVec N t (a ℓ) (M ℓ) j.val k.val i.val
  let c : ℕ := ∑ ℓ : N.primeFactors, (N + M ℓ * (1 + 2 * n * (z + ℓ.val * (M ℓ * e))))
  -- Step 1: Every `u x` lies in the lattice `𝔞₀ = E ∩ α Ô`.
  have hu_mem : ∀ x : I, finiteImage id (u x) ∈ Ô (P.E s) := fun ⟨ℓ, j, k, i⟩ ↦
    finiteImage_mem_iff.2 fun v ↦ by
      by_cases hv : P.betaKInE s ∈ v.asIdeal
      · rw [ite_eq_left hv]
        exact valuation_mul_orbitVec_le_one v hN_ne j.val k.val i.val
          ⟨t * V ℓ, by linear_combination t * hV_eq ℓ⟩
      · rw [ite_eq_right hv, one_mul]
        simpa only [map_mul, map_pow, v.valuation_eq_one_iff_notMem.2 hv, one_pow, one_mul] using
          valuation_mul_orbitVec_le_one v hN_ne j.val k.val i.val
            (dvd_mul_of_dvd_left (q₁_dvd_betaKInE_pow_mul he_eq) (M ℓ * (a ℓ - 1)))
  -- Step 2: Compute the frame Gram matrix `∑ x, Φ σ (u x) * conj (Φ τ (u x)) = δ(σ, τ) * c`.
  have h_frame_sum (σ τ : P.Φ s) :
      ∑ x : I, Φ σ (u x) * conj (Φ τ (u x)) = if σ = τ then (c : ℂ) else 0 := by
    -- Compute the contribution of each prime factor `ℓ ∣ N`.
    rw [Fintype.sum_sigma]
    have h_block (ℓ : N.primeFactors) :
        ∑ p : Fin (r ℓ) × Fin ℓ.val × Fin ℓ.val,
          Φ σ (u ⟨ℓ, p⟩) * conj (Φ τ (u ⟨ℓ, p⟩)) =
          if σ = τ then ((N + M ℓ * (1 + 2 * n * (z + ℓ.val * (M ℓ * e))) : ℕ) : ℂ) else 0 := by
      simpa only [Fintype.sum_prod_type] using sum_orbitVec_mul_conj he_eq ℓ (hN_eq ℓ) σ τ
    simp_rw [h_block]
    split_ifs <;> simp [c, N, n]
  -- Step 3: `c` is coprime to `N`.
  have hc_coprime : c.Coprime N := by
    refine Nat.coprime_of_dvd fun p hp hpc hpN ↦ ?_
    let p₀ : N.primeFactors := ⟨p, Nat.mem_primeFactors.2 ⟨hp, hpN, hN_ne⟩⟩
    have hp_n : p ∣ n := P.dvd_d_add_one_div_four_of_dvd_q₁ hp hpN
    have hN0 : (N : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff N p).2 hpN
    have hn0 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).2 hp_n
    have h_mod : (c : ZMod p) = (M p₀ : ZMod p) := by
      simp only [c, Nat.cast_sum]
      rw [Finset.sum_eq_single p₀]
      · simp [hN0, hn0]
      · intro ℓ _ hne
        have hM0 : (M ℓ : ZMod p) = 0 :=
          (ZMod.natCast_eq_zero_iff (M ℓ) p).2
            ((hM_primes ℓ p p₀.property).2 fun h ↦ hne (Subtype.ext h.symm))
        simp [hN0, hM0]
      · simp
    have hp_M : p ∣ M p₀ :=
      (ZMod.natCast_eq_zero_iff _ p).1 (h_mod.symm.trans ((ZMod.natCast_eq_zero_iff c p).2 hpc))
    exact (hM_primes p₀ p p₀.property).1 hp_M rfl
  -- Step 4: Elementary polynomial bound `c ≤ (d * N) ^ 6`.
  have hc_le : c ≤ (P.d * N) ^ 6 := sum_orbit_length_le (NeZero.pos N) hz_lt he_eq hM_le
  -- Step 5: Unit linear form for every prime `p` and embedding `ιₚ : ℂ →+* ℂ_[p]`.
  have h_unit (p : ℕ) [Fact p.Prime] [PadicPlace p] :
      P.HasUnitLinearForm s p 1 ∨ ∃ x : I, P.HasUnitLinearForm s p (u x) := by
    by_cases h1 : P.HasUnitLinearForm s p 1
    · exact .inl h1
    right
    have hp_dvd : p ∣ N := by
      by_contra hp_ndvd
      exact h1 fun τ ↦ by simp [P.norm_iota_periodFactor_eq_one s hp_ndvd]
    have hp_prime : p.Prime := Fact.out
    let ℓ : N.primeFactors := ⟨p, Nat.mem_primeFactors.2 ⟨hp_prime, hp_dvd, hN_ne⟩⟩
    have hr_pos : 0 < r ℓ := Nat.pos_of_ne_zero fun hr0 ↦ hN_ne (by simp [hN_eq ℓ, hr0])
    have h_emb (τ : P.Φ s) (y : P.E s) : weightEmbedding ιₚ τ y = ιₚ (conj (Φ τ y)) :=
      congrArg ιₚ (map_star_complex _ y)
    have hβ_mem (τ : P.Φ s) : P.betaKInE s ∈ (placeOfEmb (weightEmbedding ιₚ τ)).asIdeal := by
      by_contra h_not
      refine h1 fun τ' ↦ ?_
      have h_not' : P.betaKInE s ∉ (placeOfEmb (weightEmbedding ιₚ τ')).asIdeal := by
        simpa only [mem_placeOfEmb, h_emb, phi_betaKInE] using h_not
      simp [norm_iota_periodFactor τ', adeleExtension_alpha, h_not']
    let x₀ : I := ⟨ℓ, (⟨0, hr_pos⟩, ⟨1, hp_prime.one_lt⟩, ⟨0, hp_prime.pos⟩)⟩
    refine ⟨x₀, fun τ ↦ ?_⟩
    let φ : P.E s →+* ℂ_[p] := weightEmbedding ιₚ τ
    have h_u_eq : (P.relDifferentGen s : P.E s) * u x₀ = ((-t * V ℓ : 𝓞 (P.E s)) : P.E s) := by
      have hV_E : (P.relDifferentGen s : P.E s) * ((a ℓ : P.E s) - 1) * (M ℓ : P.E s) =
          (N : P.E s) * (V ℓ : P.E s) := by exact_mod_cast hV_eq ℓ
      simp only [u, orbitVec, x₀, pow_zero, pow_one, one_mul, zero_mul, zero_add]
      field_simp [Nat.cast_ne_zero.2 hN_ne]
      push_cast
      linear_combination -(t : P.E s) * hV_E
    rw [map_mul, norm_mul, ← h_emb τ (u x₀), norm_iota_periodFactor τ, adeleExtension_alpha,
      ite_eq_left (hβ_mem τ), norm_inv, inv_inv, ← norm_mul, ← map_mul, h_u_eq]
    refine (norm_ringOfIntegers_le φ (-t * V ℓ)).eq_of_not_lt fun h_lt ↦ ?_
    have h_mem : -t * V ℓ ∈ (placeOfEmb φ).asIdeal := (mem_placeOfEmb φ _).2 h_lt
    rcases (placeOfEmb φ).isPrime.mem_or_mem h_mem with ht | hV_mem
    · have hn_mem : (n : 𝓞 (P.E s)) ∈ (placeOfEmb φ).asIdeal := by
        rw [← P.betaKInE_mul_one_sub s]
        exact Ideal.mul_mem_right _ _ (hβ_mem τ)
      have h_one_eq : (1 : 𝓞 (P.E s)) = t + P.betaKInE s - (n : 𝓞 (P.E s)) * z := by
        dsimp only [t]
        ring
      refine (placeOfEmb φ).isPrime.one_notMem ?_
      rw [h_one_eq]
      exact sub_mem (add_mem (neg_mem_iff.1 ht) (hβ_mem τ)) (Ideal.mul_mem_right _ _ hn_mem)
    · have hM_mem : (M ℓ : 𝓞 (P.E s)) ∈ (placeOfEmb φ).asIdeal :=
        Ideal.mem_of_dvd _ (hV_dvd ℓ) hV_mem
      have hp_M : p ∣ M ℓ :=
        (FinPlace.natCast_mem_iff_dvd (placeOfEmb φ) (natCast_mem_placeOfEmb φ)).1 hM_mem
      exact (hM_primes ℓ p ℓ.property).1 hp_M rfl
  refine ⟨c, I, inferInstance, u, ⟨hu_mem, ?_⟩, hc_le, hc_coprime, h_unit⟩
  simpa using h_frame_sum

/-- Let `v` be a tight frame with multiplicities 1 of a length `h` prime to `q₁`. For every
`m ≥ q₁ h + R (q₁ + h)`, the powers `ζ ^ i`, `i < q₁`, and the members of `v` form a tight frame of
length `m` with suitable multiplicities, all at least `R`. -/
lemma exists_isTightFrame_of_coprime {h : ℕ} {I : Type} [Fintype I] {v : I → P.E s}
    (hv : IsTightFrame v 1 h) (h_coprime : h.Coprime (P.q₁ s)) {m R : ℕ}
    (h_large : P.q₁ s * h + R * (P.q₁ s + h) ≤ m) :
    ∃ c : Fin (P.q₁ s) ⊕ I → ℕ,
      IsTightFrame (Sum.elim (fun i : Fin (P.q₁ s) ↦ P.ζ s ^ i.val) v) c m ∧
      ∀ j : Fin (P.q₁ s) ⊕ I, R ≤ c j := by
  -- Every integer from `q₁ h` on is a sum of multiples of the coprime numbers `q₁` and `h`.
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, a * P.q₁ s + b * h = m - R * (P.q₁ s + h) :=
    Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le (P.q₁ s) h _
      (by simp [h_coprime.symm.gcd_eq_one])
      ((Nat.mul_le_mul (Nat.pred_le _) (Nat.pred_le _)).trans (Nat.le_sub_of_add_le h_large))
  have h_sum : (a + R) * P.q₁ s + (b + R) * h = m := by lia
  -- Take the powers of `ζ` `a + R` times and the frame `v` `b + R` times.
  have h_pow : IsTightFrame (fun i : Fin (P.q₁ s) ↦ P.ζ s ^ i.val) (fun _ ↦ a + R)
      ((a + R) * P.q₁ s) :=
    P.isTightFrame_zeta_pow s (a + R)
  have hv_mul : IsTightFrame v (fun _ ↦ b + R) ((b + R) * h) := by simpa using hv.mul_left (b + R)
  exact ⟨_, by simpa only [h_sum] using h_pow.sumElim hv_mul, by simp⟩

end Parameters

namespace Data

open Real

variable {P : Parameters} (D : Data P)

/-- Let `D` be data for the parameters `P` (a `Data P`), with field `E = D.E = P.E s` for the
exponent `s = D.towerExp`, weight `b = D.b`, and `f = D.f` the number of infinite places of `E`. The
principal level `M = D.M` is the product of the two distinct primes `D.levelPrime 0` and
`D.levelPrime 1` of the data, which lie in `[b ^ 10, b ^ 11]`. There is a tight frame `v` of length
`M` with multiplicities `c i ≥ 6 f b`. Moreover, for every prime `p` and embedding
`ιₚ : ℂ →+* ℂ_[p]`, some `y = v i` makes `periodFactor * conj (τ(y))` a unit at `ιₚ` for all `τ` in
the CM type. -/
theorem exists_isTightFrame :
    ∃ (I : Type) (_ : Fintype I) (v : I → D.E) (c : I → ℕ),
      IsTightFrame v c D.M ∧
      (∀ i : I, 6 * D.f * D.b ≤ c i) ∧
      ∀ (p : ℕ) [Fact p.Prime] [PadicPlace p], ∃ i : I, P.HasUnitLinearForm D.towerExp p (v i) := by
  obtain ⟨h, I, _, v, hv, h_le, h_coprime, h_unit⟩ := P.exists_isTightFrame_coprime D.towerExp
  -- Since `h ≤ (d q₁) ^ 6`, the threshold `q₁ h + ⌈6 f b⌉ (q₁ + h)` is at most `D.M`.
  have h_large : D.q₁ * h + ⌈6 * D.f * D.b⌉₊ * (D.q₁ + h) ≤ D.M := by
    have h_bound : (h : ℝ) ≤ D.b := by
      calc (h : ℝ) ≤ ((P.d * D.q₁) ^ 6 : ℕ) := Nat.cast_le.2 h_le
        _ ≤ D.b := D.le_of_hasLogBound
    have h_log : D.HasLogUpper h D.logB := ⟨by rwa [ite_eq_left rfl, Nat.abs_cast]⟩
    exact D.nat_le_of_hasLogBound
  let u : Fin D.q₁ ⊕ I → D.E := Sum.elim (fun i : Fin D.q₁ ↦ P.ζ D.towerExp ^ i.val) v
  obtain ⟨c, hu, hc⟩ : ∃ c : Fin D.q₁ ⊕ I → ℕ,
      IsTightFrame u c D.M ∧ ∀ j : Fin D.q₁ ⊕ I, ⌈6 * D.f * D.b⌉₊ ≤ c j :=
    Parameters.exists_isTightFrame_of_coprime hv h_coprime h_large
  refine ⟨Fin D.q₁ ⊕ I, inferInstance, u, c, hu, fun j ↦ Nat.ceil_le.1 (hc j), fun p _ _ ↦ ?_⟩
  rcases h_unit p with h1 | ⟨i, hi⟩
  · exact ⟨.inl ⟨0, NeZero.pos _⟩, by simpa [u] using h1⟩
  · exact ⟨.inr i, hi⟩

end Data

end New
