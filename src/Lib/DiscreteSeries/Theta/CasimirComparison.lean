module

public import TauCeti.Algebra.Lie.GeneralLinear.Casimir
import TauCeti.Algebra.Lie.GeneralLinear.Oscillator.Casimir
import Lib.DiscreteSeries.Theta.BlockRule
public import Lib.DiscreteSeries.Theta.FockDualPair

/-!
# The Casimir elements of an oscillator pair

An oscillator pair is given by a `FockDualPair` `T` with `n = card R` rows and `n' = card C`
columns; the first group acts on the rows. This file proves that, with the centres (the weights of
the twisting characters) removed, the Casimir elements of the two groups differ by the constant
`n n' (n - n') / 4`, and that for matching parameters the numbers `|u|² - |ρ|²` and `|u'|² - |ρ'|²`
differ by the same constant, where `u`, `u'` are the centred parameters, that is, the entries
shifted by the centres. By `HCParam.HasGap.casimirValue_sub_center` these numbers are the centred
Casimir values.

The notions that the statements use:
* a parameter `l : HCParam ε` is an integer vector that stands for `l = 2λ`; `l.HasGap h` says that
  its entries are distinct, of the parity of `n - 1`, and at least `2h` apart where the signs `ε`
  differ;
* for symmetric `r`, `twoRho l r` is the sum of the roots selected by `r` that are positive for `l`,
  so `twoRho l ⊤` is `2ρ`, and `l.casimirValue` is `|λ|² - |ρ|²`;
* `T.oscRows` is the oscillator action of `gl R` on polynomials, and `T.swap` is the same pair with
  rows and columns exchanged;
* `T.centeredParam l r` is `2u_r = l r - 2γ + n'` with `γ = T.rowShift` the scalar on the diagonal
  of the row action (`T.columnShift` is that of the column action `T.swap.oscRows`), and
  `IsMatch T l l'` says that `l` and `l'` have gap `500 (n + n')³`, that each row is matched with a
  column or has `|2u_r| < n - n'`, and that each column is matched with a row or has
  `|2u'_c| < n' - n`; the row `r` and the column `c` are matched if `u_r = -u'_c` and
  `T.globalSign * ε r * ε' c * 2u_r > |n - n'|`.

## Relation to the literature

Known result: the constant difference of the centred Casimir elements of the two groups of an
oscillator pair, a case of the correspondence of infinitesimal characters. Source: compare A. Paul,
First occurrence for the dual pairs (U(p,q), U(r,s)), Canad. J. Math. 51 (1999), Theorem 2.11.

See also `Lib.DiscreteSeries.Theta.LocalCorrespondence`.
-/

@[expose] public section

namespace New

open Finset Fock
open Fintype (card)

section SumsOfSquares

/-- The sum of the squares of `(x / 2)` over `x ∈ doubledBlock d = {d - 1, d - 3, …, 1 - d}` is
`d (d² - 1) / 12`, via `TauCeti.sum_rho_sq`. -/
private theorem sum_doubledBlock_div_two_sq (d : ℕ) :
    ∑ x ∈ doubledBlock d, ((x : ℂ) / 2) ^ 2 = (d : ℂ) * (d ^ 2 - 1) / 12 := by
  have hg : Function.Injective fun b : ℕ ↦ (d : ℤ) - 1 - 2 * b := fun j k h ↦ by simpa using h
  rw [doubledBlock, sum_image hg.injOn, ← TauCeti.sum_rho_sq (F := ℂ) d,
    Fin.sum_univ_eq_sum_range fun b : ℕ ↦ (((d : ℂ) - 1) / 2 - b) ^ 2]
  refine sum_congr rfl fun b _ ↦ ?_
  push_cast
  ring

variable {n : Type} [Fintype n]

/-- For a vector `l` with distinct entries, `twoRho l ⊤ = 2ρ` is the sum of the roots positive for
`l`. The squares of its entries sum to `N (N² - 1) / 3` with `N = card n`, that is,
`|ρ|² = N (N² - 1) / 12`. -/
theorem three_mul_sum_twoRho_sq {l : n → ℤ} (hl : l.Injective) :
    3 * ∑ i : n, twoRho l ⊤ i ^ 2 = card n * (card n ^ 2 - 1) := by
  classical
  have h_inj : Function.Injective (twoRho l ⊤) := fun a b hab ↦ by
    obtain hlt | heq | hgt := lt_trichotomy (l a) (l b)
    exacts [absurd hab (twoRho_lt_twoRho hlt).ne, hl heq,
      absurd hab (twoRho_lt_twoRho hgt).ne']
  have h_img : univ.image (twoRho l ⊤) = doubledBlock (card n) := by
    refine eq_of_subset_of_card_le (fun _ hx ↦ ?_) ?_
    · obtain ⟨i, -, rfl⟩ := mem_image.1 hx
      have h_count : #{j | l j < l i} + #{j | l i < l j} + 1 = card n :=
        card_lt_add_card_gt_add_one hl i
      refine mem_image.2 ⟨#{j | l i < l j}, mem_range.2 (by omega), ?_⟩
      simp [twoRho]
      omega
    · simp [card_image_of_injective _ h_inj, card_doubledBlock]
  have h_sum : ∑ a : n, ((twoRho l ⊤ a : ℂ) / 2) ^ 2 = (card n : ℂ) * (card n ^ 2 - 1) / 12 := by
    rw [← sum_doubledBlock_div_two_sq, ← h_img, sum_image h_inj.injOn]
  have h_cast : (3 * ∑ a : n, (twoRho l ⊤ a : ℂ) ^ 2 : ℂ) = card n * (card n ^ 2 - 1) := by
    simp only [div_pow, ← sum_div] at h_sum
    linear_combination 12 * h_sum
  exact_mod_cast h_cast

/-- For a symmetric relation `r`, the entries of `twoRho l r` sum to zero. -/
theorem sum_twoRho_eq_zero (l : n → ℤ) (r : n → n → Prop) [DecidableRel r]
    (hr : ∀ i j : n, r i j → r j i) : ∑ i : n, twoRho l r i = 0 := by
  -- Both counts run over the pairs with `r`, ordered by `l`.
  simp only [twoRho, sum_sub_distrib, card_filter, Nat.cast_sum, sub_eq_zero]
  rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp only [Iff.intro (hr j i) (hr i j)]

/-- For a parameter `l = 2λ` with a gap (distinct entries of the parity of `n - 1`, those of
different signs `ε` far apart), the lowest K-type and `λ` have the same sum of entries. -/
theorem HCParam.HasGap.two_mul_sum_lowestKType {ε : n → ℤˣ} {l : HCParam ε} {h : ℕ}
    (hg : l.HasGap h) : 2 * ∑ i : n, l.lowestKType i = ∑ i : n, l i := by
  have h_noncompact : ∑ i, twoRho l (fun i j ↦ ε i ≠ ε j) i = 0 :=
    sum_twoRho_eq_zero l _ fun i j ↦ Ne.symm
  have h_compact : ∑ i, twoRho l (fun i j ↦ ε i = ε j) i = 0 :=
    sum_twoRho_eq_zero l _ fun i j ↦ Eq.symm
  simp [mul_sum, two_mul_lowestKType hg, sum_sub_distrib, sum_add_distrib, h_noncompact, h_compact]

/-- Let `l = 2λ` be a parameter with a gap (distinct entries of the parity of `n - 1`, those of
different signs far apart), with Casimir value `κ = |λ|² - |ρ|²` and lowest K-type `μ`. For any
scalar `w`, the value with the centre `w` removed, `κ - 2w ∑ μ_a + n w²`, is
`∑ (λ_a - w)² - n (n² - 1) / 12`, where `n` is the number of entries. -/
theorem HCParam.HasGap.casimirValue_sub_center {ε : n → ℤˣ} {l : HCParam ε} {h : ℕ}
    (hg : l.HasGap h) (w : ℂ) :
    l.casimirValue - 2 * w * ∑ a : n, (l.lowestKType a : ℂ) + card n * w ^ 2 =
      ∑ a : n, (l a / 2 - w) ^ 2 - (card n * (card n ^ 2 - 1) / 12 : ℂ) := by
  have h_rho : 3 * ∑ a, (twoRho l ⊤ a : ℂ) ^ 2 = card n * (card n ^ 2 - 1) :=
    mod_cast three_mul_sum_twoRho_sq hg.injective
  have h_sum : 2 * ∑ a, (l.lowestKType a : ℂ) = ∑ a, (l a : ℂ) :=
    mod_cast hg.two_mul_sum_lowestKType
  have h_value : (l.casimirValue : ℂ) =
      (∑ a, (l a : ℂ) ^ 2 - ∑ a, (twoRho l ⊤ a : ℂ) ^ 2) / 4 := by
    simp [casimirValue, ← sum_div, sum_sub_distrib]
  have h_term (a : n) : (l a / 2 - w : ℂ) ^ 2 = (l a : ℂ) ^ 2 / 4 - w * l a + w ^ 2 := by ring
  have h_square : ∑ a, (l a / 2 - w : ℂ) ^ 2 =
      (∑ a, (l a : ℂ) ^ 2) / 4 - w * ∑ a, (l a : ℂ) + card n * w ^ 2 := by
    simp [h_term, sum_add_distrib, ← sum_div, ← mul_sum]
  rw [h_value, h_square]
  linear_combination -w * h_sum - h_rho / 12

end SumsOfSquares

section Casimir

variable {R C ι : Type} [Fintype R] [DecidableEq R] [Fintype C] {ε : R → ℤˣ} {ε' : C → ℤˣ}

omit [Fintype R] [DecidableEq R] in
/-- The centred parameters `l r - 2γ + card C` of a vector `l` with distinct entries are
distinct. -/
theorem FockDualPair.centeredParam_injective (T : FockDualPair ε ε' ι) {l : HCParam ε}
    (hl : Function.Injective l) : Function.Injective (T.centeredParam l) :=
  fun a b hab ↦ hl (by simpa [FockDualPair.centeredParam] using hab)

variable [DecidableEq C]

/-- The Casimir element with the centre `w` removed: it is formed with `E_ab - w δ_ab` in place of
`E_ab`. -/
noncomputable def GlModule.centeredCasimir {M : Type*} [AddCommGroup M] [Module ℂ M]
    (ρ : GlModule R M) (w : ℂ) : Module.End ℂ M :=
  ∑ a : R, ∑ b : R, (ρ.E a b - if a = b then w • 1 else 0) * (ρ.E b a - if b = a then w • 1 else 0)

/-- On a vector of weight `ν`, the Casimir element with the centre `w` removed is
`Ω - 2w ∑ ν_a + n w²`, where `n = card R`. Here `Ω = ρ.casimirK 1` is the full Casimir element
`∑ E_ab E_ba`: all signs are `1`, so every pair of indices counts. -/
theorem GlModule.centeredCasimir_apply {M : Type*} [AddCommGroup M] [Module ℂ M]
    (ρ : GlModule R M) (w : ℂ) {ν : R → ℤ} {v : M} (hv : ∀ a : R, ρ.E a a v = (ν a : ℂ) • v) :
    ρ.centeredCasimir w v =
      ρ.casimirK 1 v - (2 * w * ∑ a : R, (ν a : ℂ)) • v + (card R * w ^ 2) • v := by
  have h_expand : ρ.centeredCasimir w =
      ρ.casimirK 1 + (2 * -w) • ∑ a, ρ.E a a + (card R * (-w) ^ 2) • 1 := by
    have h_casimir : ρ.casimirK 1 = ∑ a, ∑ b, ρ.E a b * ρ.E b a := by
      simp [GlModule.casimir]
    rw [h_casimir, ← TauCeti.sum_add_scalar_mul_add_scalar]
    simp only [centeredCasimir, sub_eq_add_neg, neg_ite, neg_zero, neg_smul]
  simp [h_expand, hv, ← sum_smul]
  module

namespace FockDualPair

variable (T : FockDualPair ε ε' ι)

/-- The centre `w` of the action on the rows: the scalar `T.rowShift` on the diagonal is `w + n'/2`.
It is the weight of the character of the determinant by which the action is twisted. -/
noncomputable def center : ℂ := T.rowShift - card C / 2

omit [Fintype R] [Fintype C] in
/-- The canonical commutation relation `d_rc x_r'c' = x_r'c' d_rc + δ_rr' δ_cc'` of the
oscillator operators `lowerOp` and `raiseOp` at the variables of `T`. -/
theorem lower_mul_raise (r r' : R) (c c' : C) :
    lowerOp T.indexSign (T.varEquiv (r, c)) * raiseOp T.indexSign (T.varEquiv (r', c')) =
      raiseOp T.indexSign (T.varEquiv (r', c')) * lowerOp T.indexSign (T.varEquiv (r, c)) +
        if r = r' ∧ c = c' then 1 else 0 := by
  classical
  refine LinearMap.ext fun P ↦ ?_
  split_ifs with h <;> simp_all [lowerOp_raiseOp]

/-- For signs `δ` and a sign `s` (read in `ℂ`), the factor that is `1` if `δ a = δ b` and `s`
otherwise, times the same factor for `(b, a)`, is `1`. So these factors drop out of a Casimir
element. -/
theorem sign_mul_sign {n : Type*} (δ : n → ℤˣ) (s : ℤˣ) (a b : n) :
    (if δ a = δ b then 1 else s : ℂ) * (if δ b = δ a then 1 else s : ℂ) = 1 :=
  (ite_units_eq_mul_ite_units_eq s _ _ _).trans (ite_eq_left rfl)

section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The row action of the matrix unit `(a, b)` less `T.center = T.rowShift - n'/2` on the
diagonal is `T.conjVar` of `TauCeti.fockRowHom` at `E a b`, times the sign `T.globalSign` of the
pair where the signs `ε a`, `ε b` differ; here `n' = card C`. -/
theorem oscRows_E_sub_center (a b : R) :
    (T.oscRows.E a b - if a = b then T.center • 1 else 0) =
      (if ε a = ε b then 1 else T.globalSign : ℂ) •
        T.conjVar (TauCeti.fockRowHom ℂ T.rowBool (colBool ε') (Matrix.single a b 1)) := by
  rw [oscRows_E, T.oscRowsUnit_eq_fockRowHom, center, add_sub_cancel_right]

/-- The column action of the matrix unit `(a, b)` less `T.swap.center = T.columnShift - n/2` on
the diagonal is `-T.conjVar` of `TauCeti.fockColHom` at `E b a`, times the sign `T.globalSign` of
the pair where the signs `ε' a`, `ε' b` differ; here `n = card R`, and `T.swap` is `T` with rows
and columns exchanged. -/
theorem swap_oscRows_E_sub_center (a b : C) :
    (T.swap.oscRows.E a b - if a = b then T.swap.center • 1 else 0) =
      -(if ε' a = ε' b then 1 else T.globalSign : ℂ) •
        T.conjVar (TauCeti.fockColHom ℂ T.rowBool (colBool ε') (Matrix.single b a 1)) := by
  rw [swap_oscRows_E, TauCeti.fockColHom_single, map_add, map_sum]
  simp only [T.conjVar_oscRaise_mul_oscLower, glOp, apply_ite T.conjVar, map_smul, map_one,
    map_zero, T.lower_mul_raise, true_and, sum_add_distrib, sum_const, card_univ]
  obtain rfl | hab := eq_or_ne a b
  · simp only [↓reduceIte, show T.swap.center = T.columnShift - card R / 2 from rfl,
      ← Nat.cast_smul_eq_nsmul ℂ, neg_smul, one_smul]
    rw [← zsmul_one, ← Int.cast_smul_eq_zsmul ℂ]
    module
  · simp [hab, hab.symm]

/-- The Casimir element of the row action `T.oscRows` with the centre `T.center` removed is
`T.conjVar` of the image of `TauCeti.glCasimir ℂ R` under `TauCeti.fockRowHom`, where `n = card R`
and `n' = card C`. -/
theorem centeredCasimir_oscRows : T.oscRows.centeredCasimir T.center =
    T.conjVar (UniversalEnvelopingAlgebra.lift ℂ
      (TauCeti.fockRowHom ℂ T.rowBool (colBool ε')) (TauCeti.glCasimir ℂ R)) := by
  -- The sign factors cancel in the products.
  simp only [GlModule.centeredCasimir, oscRows_E_sub_center, smul_mul_smul_comm, sign_mul_sign,
    one_smul, TauCeti.lift_glCasimir, map_sum, map_mul]

/-- The Casimir element of the column action `T.swap.oscRows` with the centre `T.swap.center`
removed is `T.conjVar` of the image of `TauCeti.glCasimir ℂ C` under `TauCeti.fockColHom`, where
`n = card R` and `n' = card C`. -/
theorem centeredCasimir_swap_oscRows : T.swap.oscRows.centeredCasimir T.swap.center =
    T.conjVar (UniversalEnvelopingAlgebra.lift ℂ
      (TauCeti.fockColHom ℂ T.rowBool (colBool ε')) (TauCeti.glCasimir ℂ C)) := by
  -- The sign factors cancel in the products.
  simp only [GlModule.centeredCasimir, swap_oscRows_E_sub_center, neg_smul, neg_mul_neg,
    smul_mul_smul_comm, sign_mul_sign, one_smul, TauCeti.lift_glCasimir, map_sum, map_mul]
  -- Reorder the double sum to match `TauCeti.lift_glCasimir` for `gl C`.
  exact sum_comm

/-- The centred Casimir element of the column action `T.swap.oscRows` is that of the row action
`T.oscRows` plus the constant `n n' d₀ / 4`, where `n = card R`, `n' = card C` and `d₀ = n - n'`. -/
theorem centeredCasimir_swap_oscRows_eq_add : T.swap.oscRows.centeredCasimir T.swap.center =
    T.oscRows.centeredCasimir T.center + (card R * card C * (card R - card C) / 4 : ℂ) • 1 := by
  rw [centeredCasimir_swap_oscRows, centeredCasimir_oscRows, TauCeti.lift_fockColHom_glCasimir,
    map_add, map_smul, map_one]

end

omit [DecidableEq R] [DecidableEq C] in
/-- The squares of the centred parameters `T.centeredParam l r = l r - 2γ + n'` (with
`γ = T.rowShift`, `n' = card C`) sum to four times the sum of the squares of `λ_r - T.center`, for
`l = 2λ`. -/
theorem sum_centeredParam_sq (l : HCParam ε) :
    ∑ r : R, (T.centeredParam l r : ℂ) ^ 2 = 4 * ∑ r : R, (l r / 2 - T.center) ^ 2 := by
  rw [mul_sum]
  refine sum_congr rfl fun r _ ↦ ?_
  push_cast [center]
  ring

end FockDualPair

omit [DecidableEq R] [DecidableEq C] in
/-- For matching parameters `l`, `l'` with `card C ≤ card R` and `d = card R - card C`, the
centred row parameters `T.centeredParam l` are the disjoint union of the negated centred column
parameters `-T.swap.centeredParam l'` and `doubledBlock d`. -/
private theorem IsMatch.image_centeredParam_eq_union_doubledBlock {T : FockDualPair ε ε' ι}
    {l : HCParam ε} {l' : HCParam ε'} (hm : IsMatch T l l') (h_le : card C ≤ card R) :
    univ.image (T.centeredParam l) =
        univ.image (fun c : C ↦ -T.swap.centeredParam l' c) ∪ doubledBlock (card R - card C) ∧
      Disjoint (univ.image fun c : C ↦ -T.swap.centeredParam l' c)
        (doubledBlock (card R - card C)) := by
  let d : ℕ := card R - card C
  have hd : card R = card C + d := (Nat.add_sub_of_le h_le).symm
  have hd_int : (d : ℤ) = card R - card C := Nat.cast_sub h_le
  let a (c : C) : ℤ := -T.swap.centeredParam l' c
  let b (r : R) : ℤ := T.centeredParam l r
  have ha : a.Injective :=
    neg_injective.comp (T.swap.centeredParam_injective hm.hasGap_column.injective)
  have hb : b.Injective := T.centeredParam_injective hm.hasGap_row.injective
  have hpar (r : R) : Even (b r + d - 1) := by
    obtain ⟨q, hq⟩ : Even (l r + card R - 1) := hm.hasGap_row.parity r
    refine ⟨q - T.rowShift, ?_⟩
    simp only [b, FockDualPair.centeredParam, hd_int]
    omega
  have h_mp (r : R) (c : C) : T.IsMatchedPair l l' r c ↔
      b r = a c ∧ (d : ℤ) < ((T.globalSign * ε r) * ε' c : ℤˣ) * b r := by
    simp only [FockDualPair.IsMatchedPair, b, a, FockDualPair.varSign, pairSign, ← hd_int,
      abs_of_nonneg (Nat.cast_nonneg (α := ℤ) d)]
  have hentries : univ.image b = univ.image a ∪ doubledBlock d :=
    (entries_eq_of_exists_matched (s := ε') (t := fun r ↦ T.globalSign * ε r) hd hb hpar
      (fun r ↦ by simpa only [h_mp, ← hd_int] using hm.left r)
      (fun c ↦ by
        have h_abs : 0 ≤ |T.swap.centeredParam l' c| := abs_nonneg _
        simpa only [h_mp] using (hm.right c).resolve_right (by omega))).1
  have hdisj : Disjoint (univ.image a) (doubledBlock d) := by
    rw [← card_union_eq_card_add_card, ← hentries]
    simp [card_image_of_injective, ha, hb, card_doubledBlock, hd]
  exact ⟨hentries, hdisj⟩

omit [DecidableEq R] [DecidableEq C] in
/-- For matching parameters `l = 2λ`, `l' = 2λ'` with `card C ≤ card R`, the centred Casimir
values `|u|² - |ρ|²` and `|u'|² - |ρ'|²` differ by `n n' (n - n') / 4`. Here `u = λ - T.center`,
`u' = λ' - T.swap.center`, `n = card R` and `n' = card C`. -/
private theorem IsMatch.centered_casimirValue_eq_of_le {T : FockDualPair ε ε' ι} {l : HCParam ε}
    {l' : HCParam ε'} (hm : IsMatch T l l') (h_le : card C ≤ card R) :
    (∑ r : R, (l r / 2 - T.center) ^ 2 - card R * (card R ^ 2 - 1) / 12 +
        card R * card C * (card R - card C) / 4 : ℂ) =
      (∑ c : C, (l' c / 2 - T.swap.center) ^ 2 - card C * (card C ^ 2 - 1) / 12 : ℂ) := by
  -- The row centred parameters split disjointly into negated column parameters and `doubledBlock`.
  obtain ⟨hentries, hdisj⟩ := hm.image_centeredParam_eq_union_doubledBlock h_le
  have ha : Function.Injective (fun c : C ↦ -T.swap.centeredParam l' c) :=
    neg_injective.comp (T.swap.centeredParam_injective hm.hasGap_column.injective)
  have hb : Function.Injective (T.centeredParam l) :=
    T.centeredParam_injective hm.hasGap_row.injective
  -- Sum `(x / 2)²` over both sides; the unmatched block contributes `d (d² - 1) / 12`.
  have h_sum : ∑ x ∈ univ.image (T.centeredParam l), ((x : ℂ) / 2) ^ 2 =
      ∑ x ∈ univ.image (fun c : C ↦ -T.swap.centeredParam l' c) ∪
        doubledBlock (card R - card C), ((x : ℂ) / 2) ^ 2 :=
    congrArg (fun s : Finset ℤ ↦ ∑ x ∈ s, ((x : ℂ) / 2) ^ 2) hentries
  rw [sum_union hdisj, sum_image hb.injOn, sum_image ha.injOn,
    sum_doubledBlock_div_two_sq] at h_sum
  -- Convert the sums of `(centeredParam / 2)²` to `|u|²` and `|u'|²` via `sum_centeredParam_sq`.
  have h_row : ∑ r : R, ((T.centeredParam l r : ℂ) / 2) ^ 2 =
      ∑ r : R, (l r / 2 - T.center) ^ 2 := by
    simp only [div_pow, ← sum_div, T.sum_centeredParam_sq]
    ring
  have h_col : ∑ c : C, (((-T.swap.centeredParam l' c : ℤ) : ℂ) / 2) ^ 2 =
      ∑ c : C, (l' c / 2 - T.swap.center) ^ 2 := by
    simp only [Int.cast_neg, neg_div, neg_sq, div_pow, ← sum_div, T.swap.sum_centeredParam_sq]
    ring
  have hd_c : ((card R - card C : ℕ) : ℂ) = card R - card C := by
    rw [Nat.cast_sub h_le]
  rw [h_row, h_col, hd_c] at h_sum
  linear_combination h_sum

omit [DecidableEq R] [DecidableEq C] in
/-- For matching parameters `l = 2λ`, `l' = 2λ'` of the pair `T` (both of large gap, with centred
parameters that are opposite or small), `|u|² - |ρ|² + n n' d₀ / 4 = |u'|² - |ρ'|²`. Here
`u = λ - T.center` and `u' = λ' - T.swap.center`, with the centres `T.rowShift - n'/2` and
`T.columnShift - n/2` of the row and column actions; `|u|²` is the sum of squares, `n = card R`,
`n' = card C`, `d₀ = n - n'`, and `n (n² - 1) / 12`, `n' (n'² - 1) / 12` are `|ρ|²`, `|ρ'|²`. -/
theorem IsMatch.centered_casimirValue_eq {T : FockDualPair ε ε' ι} {l : HCParam ε}
    {l' : HCParam ε'} (hm : IsMatch T l l') :
    (∑ r : R, (l r / 2 - T.center) ^ 2 - card R * (card R ^ 2 - 1) / 12 +
        card R * card C * (card R - card C) / 4 : ℂ) =
      (∑ c : C, (l' c / 2 - T.swap.center) ^ 2 - card C * (card C ^ 2 - 1) / 12 : ℂ) := by
  -- Reduce to `card C ≤ card R` by swap; what remains is `n³ - n'³ - d₀³ = 3 n n' d₀`.
  obtain h_le | h_le := le_total (card C) (card R)
  · exact hm.centered_casimirValue_eq_of_le h_le
  · have h_swap :
        (∑ c : C, (l' c / 2 - T.swap.center) ^ 2 - card C * (card C ^ 2 - 1) / 12 +
            card C * card R * (card C - card R) / 4 : ℂ) =
          (∑ r : R, (l r / 2 - T.center) ^ 2 - card R * (card R ^ 2 - 1) / 12 : ℂ) := by
      simpa only [show T.swap.swap.center = T.center from rfl] using
        hm.swap.centered_casimirValue_eq_of_le h_le
    linear_combination -h_swap

end Casimir

end New
