module

public import New.Congruences.FirstOrder.RibetMatrices
public import New.Congruences.FirstOrder.RibetMethod

/-!
# Ribet's method to first order over a discrete valuation ring

This file proves an algebraic form of Ribet's method to first order that does not involve Galois
groups. Here `u x` (`x : Y`) is a finite family of representations of a group `G` over a discrete
valuation ring `O`; at certain `x`, `u x` is the sum of a main summand (the block) and of
characters. The file glues the matrices of tied rows for the block and for the characters, so that
one element serves the determinants of all combinations `∑ ω g (u x g - 1)`, and passes from
coefficients modulo powers of `p` to coefficients in `K/O`. The result is applied to Galois
representations in `New.Selmer.ribet_columns`.

In that application the data of `New.Selmer.exists_isCommonRibetElement_addVal_le` are as follows.
The elements `τ (j, true)` and `φ (j, true)` are a tame generator and a Frobenius element at the new
place `j`, and `τ (j, false)`, `φ (j, false)` are the inverses of their conjugates. The `δ v` are
tame generators at the old places, `γ x` acts on the summand by a scalar `y x` with `y x - 1` a
unit, `a` generates the cyclotomic quotient, `p` is `ℓ ^ ν`, and `C : O` is the cost of telling the
characters apart. The `X j` are free variables; only the coefficients of the monomials that divide
`∏ X j` are read.

## Main definitions and results

* `New.Selmer.exists_isCommonRibetElement_addVal_le`: the determinants of all combinations
  `∑ ω g (u x g - 1)` have one Ribet element whose coefficient comes from `O` and has bounded
  valuation. The proof finds matrices of tied rows with bounded determinant on the block
  (`TieSystem.exists_tiedRows_addVal_det_le`) and on the characters
  (`TieSystem.exists_characterRows`), and glues them (`exists_traceIdeal_multiplier_eq_sum_det`).
* `New.Selmer.exists_traceIdeal_multiplier_eq_sum_det`: the gluing, on the set where `u x` is the
  block `ρ x` plus the characters `ξ e`, with `ξ 0 = 1`.

Notions from other files:
* `New.Selmer.ribetCocyclesIn u ρ B`: the cocycles `G → B^d` for `ρ` that obey the linear relations
  among the families `(u x g - 1)_x`.
* `New.Selmer.IsCommonRibetElement` (`FittingBlock`): one `f : S` that serves as Ribet element for
  a family `β` of functions `β i : Y → L`.
* `New.Selmer.IsTraceIdeal` (`FittingBlock`): `S` holds the characteristic polynomials, and the
  `S`-module `𝒥` holds the traces of given relations.
* `New.Selmer.TieSystem`, `New.Selmer.TieSystem.tiedRows` (`RibetMatrices`): the tie system and the
  rows whose element `∑ r i (gen i - 1)` lies in the tie ideal.
-/

@[expose] public section

section RibetFirstOrder

namespace New.Selmer

open IsDiscreteValuationRing Matrix Module Submodule Polynomial MonoidAlgebra Finset Sum
  CompleteLattice

open Finsupp (linearCombination)

open MvPolynomial hiding X C aeval eval funext comap ext

section Steps

variable {O L Y G J σ W : Type} [CommRing O] [CommRing L] [Algebra O L] [Fintype σ] [DecidableEq σ]
  [Group G] (u : Y → G →* Matrix σ σ O) {S : Subalgebra O (Y → MvPolynomial J L)}
  (𝒥 : Submodule S (Y → MvPolynomial J L))

/-! ### The gluing -/

/-- If `u x` is, after reindexing by `blockEquiv`, the block `ρ` plus the characters `ξ e`, then so
is its extension to `O[X j][G]` (`polyAction`, and `polyChar` for the characters). -/
lemma polyAction_eq_reindex {r : Type} [Fintype r] [DecidableEq r] {t : ℕ}
    (blockEquiv : r ⊕ Fin t ≃ σ) {x : Y} {ρ : G →* Matrix r r O} {ξ : Fin t → G →* O}
    (hu : ∀ g : G, u x g = reindex blockEquiv blockEquiv
      (fromBlocks (ρ g) 0 0 (diagonal fun e : Fin t ↦ ξ e g)))
    (c : (MvPolynomial J O)[G]) :
    polyAction J (u x) c = reindex blockEquiv blockEquiv
      (fromBlocks (polyAction J ρ c) 0 0 (diagonal fun e : Fin t ↦ polyChar J (ξ e) c)) := by
  rw [← Equiv.symm_apply_eq]
  ext1 (i | i) (j | j)
  · simp [polyAction, hu, lift_apply, Finsupp.sum, Matrix.sum_apply]
  · simp [polyAction, hu, lift_apply, Finsupp.sum, Matrix.sum_apply]
  · simp [polyAction, hu, lift_apply, Finsupp.sum, Matrix.sum_apply]
  · simp [polyAction, polyChar, hu, lift_apply, diagonal, apply_ite (Algebra.ofId O _),
      Finsupp.sum, Matrix.sum_apply]

/-- If the `z g` are coordinates of the `u · g - 1` (`AreCoordinates`), then under every `u x` the
value of the row `∑ ω g z g` (`rowValue`, `coordRows`) has the determinant of
`∑ ω g (u x g - 1)`, read in `L[X j]`. -/
lemma det_polyAction_rowValue {ι : Type} [Fintype ι] {gen : ι → G} {z : G → ι → O}
    (hz : AreCoordinates u gen z) (ω : G →₀ O) :
    (fun x : Y ↦ MvPolynomial.map (algebraMap O L) (polyAction J (u x)
      (rowValue J gen (coordRows J ι (linearCombination O z ω)))).det) =
      fun x : Y ↦
        MvPolynomial.C (algebraMap O L (linearCombination O (fun g : G ↦ u x g - 1) ω).det) := by
  funext x
  have h_comb : Fintype.linearCombination O (fun i x ↦ u x (gen i) - 1)
      (linearCombination O z ω) x = linearCombination O (fun g : G ↦ u x g - 1) ω := by
    simp [hz, linearCombination, Finsupp.sum]
  rw [polyAction_rowValue_coordRows, h_comb]
  simp [det_apply']

/-- If the rows of `R` are tied for `T` and `𝒥` is a trace ideal for `T`, then the value
`∑ R j i (gen i - 1)` of row `j` is `b + m T.ρ₀`, with `b ∈ traceLeftIdeal T.u 𝒥` and `m` in the
left ideal of the `gen i - 1`. -/
lemma exists_mulVec_eq_add_mul_of_mem_tiedRows (T : TieSystem O Y G J σ) {ι : Type} [Fintype ι]
    {gen : ι → G} {z : G → ι → O} (hz : AreCoordinates T.u gen z)
    (h𝒥 : IsTraceIdeal 𝒥 (fun x : Y ↦ T.u x) T.p T.τ T.φ Prod.fst T.ε)
    {R : Matrix ι ι (MvPolynomial J O)[G]} (hR : ∀ j : ι, R j ∈ T.tiedRows gen) (j : ι) :
    ∃ b ∈ traceLeftIdeal T.u 𝒥, ∃ m ∈ span (MvPolynomial J O)[G]
          (Set.range (MonoidAlgebra.of (MvPolynomial J O) G ∘ gen - 1)),
        (R *ᵥ (MonoidAlgebra.of (MvPolynomial J O) G ∘ gen - 1)) j = b + m * T.ρ₀ := by
  let V : (ι → (MvPolynomial J O)[G]) →ₗ[(MvPolynomial J O)[G]] (MvPolynomial J O)[G] :=
    rowValue J gen
  have V_mem (w : ι → (MvPolynomial J O)[G]) :
      V w ∈ span (MvPolynomial J O)[G]
        (Set.range (MonoidAlgebra.of (MvPolynomial J O) G ∘ gen - 1)) := by
    simp only [V, rowValue, Fintype.linearCombination_apply]
    exact sum_mem fun i _ ↦ smul_mem _ _ (subset_span ⟨i, rfl⟩)
  have h_gen (g : G) : ∃ m ∈ span (MvPolynomial J O)[G]
      (Set.range (MonoidAlgebra.of (MvPolynomial J O) G ∘ gen - 1)),
      ∀ x : Y, polyAction J (T.u x) (.single g 1) = polyAction J (T.u x) m + 1 := by
    refine ⟨V (coordRows J ι (z g)), V_mem _, fun x ↦ ?_⟩
    rw [polyAction_rowValue_coordRows, hz g, polyAction_single, one_smul, map_sub, map_one,
      sub_add_cancel]
  obtain ⟨b, hb, h_rest⟩ := mem_sup.1 (T.tieIdeal_le 𝒥 h𝒥 (mem_comap.1 (hR j)))
  obtain ⟨_, ⟨m, hm, rfl⟩, h_sum⟩ := h_rest
  have h_row : (R *ᵥ (MonoidAlgebra.of (MvPolynomial J O) G ∘ gen - 1)) j = V (R j) := by
    simp [V, rowValue, mulVec, dotProduct, Fintype.linearCombination_apply]
  have h_aug (g : G) : polyChar J (1 : G →* O) (.single g 1) = 1 := by simp [polyChar_single]
  rw [h_row, ← h_sum]
  exact exists_mem_span_add_mul_eq_add_mul 𝒥 (MvPolynomial.map (algebraMap O L))
    (fun x ↦ polyAction J (T.u x)) (polyChar J 1) h_aug _ h_gen T.ρ₀ hb (RingHom.mem_ker.1 hm)

/-- If `u x` is a block `ρ` plus characters `ξ e` with `ξ 0 = 1`, every combination
`∑ ω g (u x g - 1)` has determinant zero: its column at `ξ 0` is zero. -/
lemma det_linearCombination_sub_one_eq_zero {r : Type} {t : ℕ} [NeZero t]
    (blockEquiv : r ⊕ Fin t ≃ σ) {x : Y} {ρ : G → Matrix r r O} {ξ : Fin t → G →* O} (hξ₀ : ξ 0 = 1)
    (hu : ∀ g : G, u x g = reindex blockEquiv blockEquiv
      (fromBlocks (ρ g) 0 0 (diagonal fun e : Fin t ↦ ξ e g)))
    (ω : G →₀ O) : (linearCombination O (fun g : G ↦ u x g - 1) ω).det = 0 := by
  have h_column (g : G) (i : σ) :
      u x g i (blockEquiv (inr 0)) = (1 : Matrix σ σ O) i (blockEquiv (inr 0)) := by
    obtain ⟨i | i, rfl⟩ := blockEquiv.surjective i
    · simp [hu]
    · simp +contextual [hu, hξ₀, Matrix.one_apply, diagonal_apply]
  refine det_eq_zero_of_column_eq_zero (blockEquiv (inr 0)) fun i ↦ ?_
  simp [Finsupp.linearCombination_apply, Finsupp.sum, Matrix.sum_apply, h_column]

/-- The gluing: given matrices `B₀` and `M i` of tied rows for `T`, a projector `k` onto the
characters, and `q₀` equal to `μ₀` on `ξ 0` and `0` on the other characters, one `f : S` multiplies
the determinants of all `∑ ω g (T.u x g - 1)` (which themselves lie in `S`) into `𝒥`, and on `𝓧`
its value is `∑ wt i μ₀ det (B₀ on the block) ∏ det (M i on ξ e)`. -/
lemma exists_traceIdeal_multiplier_eq_sum_det (T : TieSystem O Y G J σ) {r : Type}
    [Fintype r] [DecidableEq r] {t : ℕ} [NeZero t] (blockEquiv : r ⊕ Fin t ≃ σ) {𝓧 : Set Y}
    (ρ : 𝓧 → G →* Matrix r r O) {ξ : Fin t → G →* O}
    (hu_block : ∀ (x : 𝓧) (g : G),
      T.u x g = reindex blockEquiv blockEquiv
        (fromBlocks (ρ x g) 0 0 (diagonal fun e : Fin t ↦ ξ e g)))
    (h𝒥 : IsTraceIdeal 𝒥 (fun x : Y ↦ T.u x) T.p T.τ T.φ Prod.fst T.ε)
    {ι : Type} [Fintype ι] [DecidableEq ι] {gen : ι → G} {z : G → ι → O}
    (hz : AreCoordinates T.u gen z) {k q₀ : (MvPolynomial J O)[G]}
    (hkξ : ∀ e : Fin t, polyChar J (ξ e) k = 1) (hkρ : ∀ x : 𝓧, polyAction J (ρ x) k = 0)
    {μ₀ : MvPolynomial J O} (hq₀ : ∀ e : Fin t, polyChar J (ξ e) q₀ = if e = 0 then μ₀ else 0)
    (hη₀ : polyChar J (ξ 0) T.ρ₀ = 0) (B₀ : Matrix ι ι (MvPolynomial J O)[G])
    (hB₀ : ∀ i : ι, B₀ i ∈ T.tiedRows gen) {κ : Type} [Fintype κ] (wt : κ → MvPolynomial J O)
    (M : κ → Matrix ι ι (MvPolynomial J O)[G]) (hM : ∀ (i : κ) (j : ι), M i j ∈ T.tiedRows gen) :
    (∀ ω : G →₀ O, (fun x : Y ↦ MvPolynomial.C
      (algebraMap O L (linearCombination O (fun g : G ↦ T.u x g - 1) ω).det)) ∈ S) ∧
    ∃ f : S,
      (∀ ω : G →₀ O, (f : Y → MvPolynomial J L) * (fun x : Y ↦ MvPolynomial.C
        (algebraMap O L (linearCombination O (fun g : G ↦ T.u x g - 1) ω).det)) ∈ 𝒥) ∧
      ∀ x : 𝓧, (f : Y → MvPolynomial J L) x =
        MvPolynomial.map (algebraMap O L) (∑ i : κ, wt i * (μ₀ *
          (Matrix.comp ι ι r r (MvPolynomial J O) (B₀.map (polyAction J (ρ x)))).det *
            ∏ e : Fin t, ((M i).map (polyChar J (ξ e))).det)) := by
  let _ : Algebra (MvPolynomial J O) (MvPolynomial J L) := algebraMvPolynomial
  let Λ : Type := MvPolynomial J O
  have h_alg : algebraMap Λ (MvPolynomial J L) = MvPolynomial.map (algebraMap O L) := rfl
  let χ (x : Y) : Λ[G] →ₐ[Λ] Matrix σ σ Λ := polyAction J (T.u x)
  let ψ (x : 𝓧) : Λ[G] →ₐ[Λ] Matrix r r Λ := polyAction J (ρ x)
  let η (e : Fin t) : Λ[G] →ₐ[Λ] Λ := polyChar J (ξ e)
  let gen_sub_one : ι → Λ[G] := MonoidAlgebra.of Λ G ∘ gen - 1
  -- Lift `Λ = O[X j]` to `S` via the constant families `X j ∈ S`.
  let X' : J → S := fun j ↦ ⟨fun _ ↦ MvPolynomial.X j, h𝒥.X_mem j⟩
  let κS : Λ →+* S := (MvPolynomial.aeval X').toRingHom
  have hκS : (algebraMap S (Y → MvPolynomial J L)).comp κS =
      algebraMap Λ (Y → MvPolynomial J L) := by
    refine MvPolynomial.ringHom_ext (fun c ↦ funext fun _ ↦ ?_) (fun j ↦ funext fun _ ↦ ?_)
    · simp only [RingHom.comp_apply, κS, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_C]
      exact (MvPolynomial.map_C (algebraMap O L) c).symm
    · simp only [RingHom.comp_apply, κS, X', AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X, Subalgebra.algebraMap_apply]
      exact (MvPolynomial.map_X (algebraMap O L) j).symm
  have hχ_coeff (g : G) (n : ℕ) :
      (fun x ↦ ((χ x (.single g 1)).map (algebraMap Λ (MvPolynomial J L))).charpoly.coeff n) ∈
        S := by
    have h_map (x : Y) : (χ x (.single g 1)).map (algebraMap Λ (MvPolynomial J L)) =
        (T.u x g).map (MvPolynomial.C.comp (algebraMap O L)) := by
      ext1 i j
      rw [Matrix.map_apply, Matrix.map_apply, h_alg,
        show χ x (.single g 1) = (Algebra.ofId O (MvPolynomial J O)).mapMatrix (T.u x g) by
          simpa [χ] using polyAction_single (J := J) (T.u x) g 1]
      exact MvPolynomial.map_C (algebraMap O L) (T.u x g i j)
    simpa only [h_map, charpoly_map, Polynomial.coeff_map, RingHom.comp_apply] using
      h𝒥.charpoly_coeff_mem g n
  have h_det_mem (ω : G →₀ O) : (fun x : Y ↦ MvPolynomial.C
      (algebraMap O L (linearCombination O (fun g : G ↦ T.u x g - 1) ω).det)) ∈ S := by
    obtain ⟨ρS, hρS, h_charpoly⟩ := exists_family_algHom_charpoly_mem χ κS hκS hχ_coeff
    obtain ⟨D, hD, -⟩ := Selmer.exists_mul_eq_algebraMap_det χ κS ρS hρS h_charpoly
      (rowValue J gen (coordRows J ι (linearCombination O z ω)))
    have h_eq : (fun x : Y ↦ MvPolynomial.map (algebraMap O L) (polyAction J (T.u x)
        (rowValue J gen (coordRows J ι (linearCombination O z ω)))).det) = D := hD.symm
    rw [← det_polyAction_rowValue T.u hz, h_eq]
    exact D.prop
  have hψ₁ (x : 𝓧) : ψ x (k * q₀) = 0 := by simp [ψ, hkρ]
  have hη₁ (e : Fin t) : η e (k * q₀) = if e = 0 then μ₀ else 0 := by simp [η, hkξ, hq₀]
  have h_tied (i : κ) (j : ι) : ((1 - k) • B₀ + k • M i) j ∈ T.tiedRows gen :=
    add_mem ((T.tiedRows gen).smul_mem _ (hB₀ j)) ((T.tiedRows gen).smul_mem _ (hM i j))
  have exists_f (i : κ) : ∃ f : S,
      (∀ w ∈ span Λ[G] (Set.range gen_sub_one),
        f.val * (fun x ↦ algebraMap Λ (MvPolynomial J L) (χ x w).det) ∈ 𝒥) ∧
      ∀ x : 𝓧, f.val x = algebraMap Λ (MvPolynomial J L) (μ₀ *
        (Matrix.comp ι ι r r Λ (((1 - k) • B₀ + k • M i).map (ψ x))).det *
        ∏ e, (((1 - k) • B₀ + k • M i).map (η e)).det) :=
    Selmer.exists_ribet_element_of_tied_rows blockEquiv χ κS hκS hχ_coeff 𝒥 gen_sub_one
      T.ρ₀ (k * q₀) ((1 - k) • B₀ + k • M i)
      (exists_mulVec_eq_add_mul_of_mem_tiedRows 𝒥 T hz h𝒥 (h_tied i))
      ψ η (fun x ↦ polyAction_eq_reindex T.u blockEquiv (hu_block x)) hψ₁ hη₁ hη₀
  choose f hf_mem hf_eq using exists_f
  refine ⟨h_det_mem, ∑ i, κS (wt i) * f i, fun ω ↦ ?_, fun x ↦ ?_⟩
  · let w : Λ[G] := rowValue J gen (coordRows J ι (linearCombination O z ω))
    have hw : w ∈ span Λ[G] (Set.range gen_sub_one) := by
      simp only [w, rowValue, Fintype.linearCombination_apply]
      exact sum_mem fun j _ ↦ smul_mem _ _ (subset_span ⟨j, rfl⟩)
    rw [← det_polyAction_rowValue T.u hz, ← smul_eq_mul, ← Subalgebra.smul_def, Finset.sum_smul]
    refine sum_mem fun i _ ↦ ?_
    rw [mul_smul, Subalgebra.smul_def (f i), smul_eq_mul]
    exact 𝒥.smul_mem _ (hf_mem i w hw)
  · -- On `𝓧`, `(1 - k) • B₀ + k • M i` is `B₀` on the block and `M i` on the characters.
    have hκS_apply (c : Λ) : (κS c).val x = algebraMap Λ (MvPolynomial J L) c :=
      congrFun (RingHom.congr_fun hκS c) x
    have h_block (i : κ) : ((1 - k) • B₀ + k • M i).map (ψ x) = B₀.map (ψ x) := by
      ext1
      simp [ψ, hkρ]
    have h_chars (i : κ) (e : Fin t) : ((1 - k) • B₀ + k • M i).map (η e) = (M i).map (η e) := by
      ext1
      simp [η, hkξ]
    simp [hf_eq, hκS_apply, h_block, h_chars, map_sum, ψ, η, Λ]

/-- The projector to the characters: if every block `ρ x` has an element `γ x` acting by a scalar
`y x` with `y x - 1` a unit, on which every character is `1`, then some element of `O[X j][G]` is
`1` on every character and `0` on every block. -/
lemma exists_character_projector {r : Type} [Fintype r] [DecidableEq r] {t : ℕ}
    {𝓧 : Type} [Fintype 𝓧] (ρ : 𝓧 → G →* Matrix r r O) {ξ : Fin t → G →* O} {γ : 𝓧 → G} {y : 𝓧 → O}
    (hργ : ∀ x : 𝓧, ρ x (γ x) = y x • 1) (hy_unit : ∀ x : 𝓧, IsUnit (y x - 1))
    (hξγ : ∀ (x : 𝓧) (e : Fin t), ξ e (γ x) = 1) :
    ∃ k : (MvPolynomial J O)[G],
      (∀ e : Fin t, polyChar J (ξ e) k = 1) ∧
      ∀ x : 𝓧, polyAction J (ρ x) k = 0 := by
  refine exists_forall_eq_one_and_forall_eq_zero (fun e ↦ polyChar J (ξ e))
    (fun x ↦ polyAction J (ρ x)) fun x ↦ ?_
  obtain ⟨c, hc⟩ : ∃ c : O, c * (y x - 1) = 1 := (hy_unit x).exists_left_inv
  let w : (MvPolynomial J O)[G] :=
    (MvPolynomial.C (y x) : MvPolynomial J O) • 1 - MonoidAlgebra.single (γ x) 1
  have h_char (e : Fin t) : polyChar J (ξ e) w = MvPolynomial.C (y x - 1) := by
    simp [w, polyChar_single, hξγ]
  have h_block : polyAction J (ρ x) w = 0 := by
    simp [w, polyAction_single, hργ, smul_one_eq_diagonal]
  refine ⟨(MvPolynomial.C c : MvPolynomial J O) • w, fun e ↦ ?_, ?_⟩
  · rw [map_smul, h_char, smul_eq_mul, ← map_mul, hc, map_one]
  · rw [map_smul, h_block, smul_zero]

/-- Finitely many generators. Let `u x` (`x : Y`) be finitely many matrix representations of `G`
over the discrete valuation ring `O`. There are a finite `s₀ ⊆ G` and vectors `z g` over `O` with
`u x g - 1 = ∑ z g i (u x (gen i) - 1)` for all `g` and `x` (`AreCoordinates`), where `gen` lists
the `δ w`, the members of `s₀` and those of `s` (`ribetGenerators`). -/
lemma exists_areCoordinates_ribetGenerators (u : Y → G →* Matrix σ σ O) [DVR O] [Fintype Y]
    [Fintype W] (δ : W → G) (s : Finset G) :
    ∃ (s₀ : Finset G) (z : G → W ⊕ s₀ ⊕ s → O),
      AreCoordinates u (ribetGenerators δ s₀ s) z := by
  classical
  let v (g : G) : Y → Matrix σ σ O := fun x ↦ u x g - 1
  have h_compact : IsCompactElement (⨆ g : G, O ∙ v g) := (fg_iff_compact _).1 .of_finite
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Finset G, ⨆ g : G, (O ∙ v g) ≤ ⨆ g ∈ s₀, (O ∙ v g) :=
    h_compact.exists_finset_of_le_iSup _ le_rfl
  let gen : W ⊕ s₀ ⊕ s → G := ribetGenerators δ s₀ s
  let T : (W ⊕ s₀ ⊕ s → O) →ₗ[O] Y → Matrix σ σ O :=
    Fintype.linearCombination O fun i ↦ v (gen i)
  have h_range : ⨆ g ∈ s₀, (O ∙ v g) ≤ T.range := by
    refine iSup₂_le fun g hg ↦ ?_
    rw [span_singleton_le_iff_mem]
    exact ⟨Pi.single (inr (inl ⟨g, hg⟩)) 1, by simp [T, gen]⟩
  have exists_z (g : G) : ∃ m : W ⊕ s₀ ⊕ s → O, T m = v g :=
    LinearMap.mem_range.1 (hs₀.trans h_range (mem_iSup_of_mem g (mem_span_singleton_self _)))
  choose z hz using exists_z
  exact ⟨s₀, z, hz⟩

end Steps

section Lemma

variable {O L Y G J σ W : Type} [CommRing O] [CommRing L] [Algebra O L] [Fintype σ] [DecidableEq σ]
  [Group G] (u : Y → G →* Matrix σ σ O) {S : Subalgebra O (Y → MvPolynomial J L)}
  (𝒥 : Submodule S (Y → MvPolynomial J L))

/-- Membership in `ribetCocyclesIn`: `c` is a cocycle for `ρ`, and it obeys every linear relation
among the families `u · g - 1`. -/
lemma mem_ribetCocyclesIn_iff {r : Type} [Fintype r] [DecidableEq r] {ρ : G →* Matrix r r O}
    {B : Type} [AddCommGroup B] [Module O B] {c : G → r → B} :
    c ∈ ribetCocyclesIn u ρ B ↔ c ∈ obeying (cocycleRelations ρ) B ∧ ∀ θ : G →₀ O,
      linearCombination O (fun (g : G) (x : Y) ↦ u x g - 1) θ = 0 → linearCombination O c θ = 0 :=
  Iff.rfl

/-- Let `u x` (`x : Y`) be matrix representations of the group `G` over `O`, and let `f` be an
injective linear map of coefficient modules. Then `c` is a cocycle for `ρ` with `∑ θ g • c g = 0`
whenever `∑ θ g • (u x g - 1) = 0` for all `x` (`ribetCocyclesIn`) if and only if `f ∘ c` is one. -/
lemma comp_mem_ribetCocyclesIn_iff (u : Y → G →* Matrix σ σ O) {r : Type} [Fintype r]
    [DecidableEq r]
    {ρ : G →* Matrix r r O} {B B' : Type} [AddCommGroup B] [Module O B] [AddCommGroup B']
    [Module O B'] {f : B →ₗ[O] B'} (hf : Function.Injective f) {c : G → r → B} :
    (fun (g : G) (i : r) ↦ f (c g i)) ∈ ribetCocyclesIn u ρ B' ↔ c ∈ ribetCocyclesIn u ρ B := by
  have h_lc (θ : G →₀ O) : linearCombination O (fun (g : G) (i : r) ↦ f (c g i)) θ =
      fun i : r ↦ f (linearCombination O c θ i) := by
    ext i
    simp [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
  have h_obey : (fun (g : G) (i : r) ↦ f (c g i)) ∈ obeying (cocycleRelations ρ) B' ↔
      c ∈ obeying (cocycleRelations ρ) B := by
    rw [comp_mem_obeying_iff, mem_obeying]
    refine forall₂_congr fun F _ ↦ ?_
    simp only [map_eq_zero_iff f hf, funext_iff, Pi.zero_apply]
  rw [mem_ribetCocyclesIn_iff, mem_ribetCocyclesIn_iff]
  refine and_congr h_obey (forall₂_congr fun θ _ ↦ ?_)
  simp only [h_lc, map_eq_zero_iff f hf, funext_iff, Pi.zero_apply]

/-- Let `u x` be a finite family of representations of `G` over a discrete valuation ring `O` with
fraction field `K`. The cocycles of `ρ` with values in `K/O` that obey the linear relations among
the families `(u x g - 1)_x` are torsion: by the coordinates of
`exists_areCoordinates_ribetGenerators` the values of a member are combinations of finitely many of
them, and each element of `K/O` has a nonzero denominator. -/
lemma exists_smul_eq_zero_of_mem_ribetCocyclesIn [DVR O] [Fintype Y] {r : Type} [Fintype r]
    [DecidableEq r] {ρ : G →* Matrix r r O} {c : G → r → DivisibleQuot O}
    (hc : c ∈ ribetCocyclesIn u ρ (DivisibleQuot O)) : ∃ a : O, a ≠ 0 ∧ a • c = 0 := by
  classical
  obtain ⟨-, h_rel⟩ := (mem_ribetCocyclesIn_iff u).1 hc
  choose d hd_ne hd using fun y : DivisibleQuot O ↦ exists_smul_eq_zero_divisibleQuot y
  obtain ⟨s₀, z, hz⟩ := exists_areCoordinates_ribetGenerators u Empty.elim ∅
  let gen : Empty ⊕ s₀ ⊕ (∅ : Finset G) → G := ribetGenerators Empty.elim s₀ ∅
  have h_val (g : G) : c g = ∑ i : Empty ⊕ s₀ ⊕ (∅ : Finset G), z g i • c (gen i) := by
    have h_g : Fintype.linearCombination O (fun i x ↦ u x (gen i) - 1) (z g) =
        fun x ↦ u x g - 1 := hz g
    have hθ : linearCombination O (fun (g : G) (x : Y) ↦ u x g - 1)
        (Finsupp.single g 1 - ∑ i : Empty ⊕ s₀ ⊕ (∅ : Finset G), Finsupp.single (gen i) (z g i)) =
          0 := by
      simp [map_sub, map_sum, Finsupp.linearCombination_single, ← h_g,
        Fintype.linearCombination_apply]
    simpa [map_sub, map_sum, Finsupp.linearCombination_single, sub_eq_zero] using h_rel _ hθ
  let a : O := ∏ i : Empty ⊕ s₀ ⊕ (∅ : Finset G), ∏ k : r, d (c (gen i) k)
  refine ⟨a, ?_, funext₂ fun g k ↦ ?_⟩
  · simp [a, Finset.prod_ne_zero_iff, hd_ne]
  · simp only [Pi.smul_apply, Pi.zero_apply, h_val g, Finset.sum_apply, Finset.smul_sum]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    obtain ⟨e, he⟩ : ∃ e : O, a = d (c (gen i) k) * e :=
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)).trans
        (Finset.dvd_prod_of_mem (fun i ↦ ∏ k : r, d (c (gen i) k)) (Finset.mem_univ i))
    rw [smul_comm, he, mul_comm, mul_smul, hd, smul_zero, smul_zero]

/-- From coefficients modulo powers of `p` to coefficients in `K/O = Frac(O) / O`. Let `u x` be a
finite family of representations of `G` over `O`. Consider the cocycles `c` of `ρ` that vanish on
`T` and at `γ` and have `∑ θ g • c g = 0` whenever `∑ θ g • (u x g - 1) = 0` for all `x`. It
suffices to bound the length by `b` at the single level `a = p ^ (b + 1)`, where `p ≠ 0` is not a
unit. Division by `a` maps the cocycles modulo `a` onto the `a`-torsion; as `v(a) > b`, this
torsion is everything. No uniform bound over all truncation levels is needed. -/
lemma length_ribetCocyclesVanishingOn_divisibleQuot_le [DVR O] [Fintype Y] {r : Type}
    [Fintype r] [DecidableEq r] (ρ : G →* Matrix r r O) (T : Set G) (γ : G) {p : O} (hp : p ≠ 0)
    (hp_unit : ¬IsUnit p) {b : ℕ}
    (h_length_pow : length O (ribetCocyclesVanishingOn u ρ (QuotSpan (p ^ (b + 1))) T γ) ≤ b) :
    length O (ribetCocyclesVanishingOn u ρ (DivisibleQuot O) T γ) ≤ b := by
  set V : Submodule O (G → r → DivisibleQuot O) :=
    ribetCocyclesVanishingOn u ρ (DivisibleQuot O) T γ
  let a : O := p ^ (b + 1)
  have ha : a ≠ 0 := pow_ne_zero _ hp
  let E : (G → r → QuotSpan a) →ₗ[O] G → r → DivisibleQuot O :=
    ((divQuot a).compLeft r).compLeft G
  have h_le : (torsionBy O V a).map V.subtype ≤
      (ribetCocyclesVanishingOn u ρ (QuotSpan a) T γ).map E := by
    rintro _ ⟨⟨c, hcV⟩, hc_tors, rfl⟩
    have hc_smul : a • c = 0 := congrArg Subtype.val ((mem_torsionBy_iff a _).1 hc_tors)
    choose c' hc' using fun (g : G) (i : r) ↦ exists_divQuot_eq ha (congrFun₂ hc_smul g i)
    have h_zero {g : G} (hg : c g = 0) : c' g = 0 :=
      funext fun i ↦ divQuot_injective ha (by simp [hc', hg])
    obtain ⟨h_obey, h_T, h_γ⟩ := (mem_ribetCocyclesVanishingOn u).1 hcV
    refine ⟨c', (mem_ribetCocyclesVanishingOn u).2
      ⟨?_, fun g hg ↦ h_zero (h_T g hg), h_zero h_γ⟩, funext₂ hc'⟩
    rw [← comp_mem_ribetCocyclesIn_iff u (divQuot_injective ha)]
    simpa only [hc'] using h_obey
  have h_length : length O (torsionBy O V a) ≤ b := by
    rw [(Submodule.equivMapOfInjective V.subtype V.injective_subtype _).length_eq]
    exact (length_le_of_le_map E _ h_le).trans h_length_pow
  -- Every member of `V` is torsion and `v(a) ≥ b + 1`, so the `a`-torsion is all of `V`.
  have h_torsion : ∀ w : V, ∃ a' : O, a' ≠ 0 ∧ a' • w = 0 := by
    rintro ⟨c, hcV⟩
    obtain ⟨h_obey, -⟩ := (mem_ribetCocyclesVanishingOn u).1 hcV
    obtain ⟨a', ha', ha'c⟩ := exists_smul_eq_zero_of_mem_ribetCocyclesIn u h_obey
    exact ⟨a', ha', Subtype.ext ha'c⟩
  have h_va : (b : ℕ∞) + 1 ≤ addVal O a := by
    have h_one : 1 ≤ addVal O p := Order.one_le_iff_ne_zero.2 fun h_val_zero ↦
      hp_unit (addVal_eq_zero_iff.1 h_val_zero)
    calc (b : ℕ∞) + 1 = (b + 1 : ℕ) • (1 : ℕ∞) := by simp
      _ ≤ (b + 1 : ℕ) • addVal O p := nsmul_le_nsmul_right h_one _
      _ = addVal O a := (addVal_pow p (b + 1)).symm
  have h_top : torsionBy O V a = ⊤ := by
    by_contra h_ne
    have h_cast : ((b + 1 : ℕ) : ℕ∞) ≤ b := by
      rw [Nat.cast_succ]
      exact h_va.trans ((addVal_le_length_torsionBy h_torsion h_ne).trans h_length)
    exact absurd (Nat.cast_le.1 h_cast) (by omega)
  rw [← length_top, ← h_top]
  exact h_length

/-- Ribet's lemma to first order, for any group and any discrete valuation ring. Let `u x` (`x : Y`)
be a finite family of matrix representations of `G` over `O` and `L` an `O`-algebra; let `S` be an
algebra of families `Y → L[X j]`, where `L[X j]` is `MvPolynomial J L`, and `𝒥` an `S`-module of
such families. (1) On `𝓧`, `u x` is, after reindexing along `blockEquiv`, a block `ρ x` plus
characters `ξ e` with `ξ 0 = 1`, and `ρ π` spans all matrices. (2) An element `γ x` acts on the
block by a scalar `y x` with `y x - 1` a unit, and trivially on the characters. (3) For `p ≠ 0` in
`O`, elements `τ k`, `φ k` of `G` (`k : J × Bool`) and polynomials `ε j` over `O`, `S` contains the
`X j` and the coefficients of the characteristic polynomials of the `u x g`, and `𝒥` contains the
families over `x` of the traces under `u x` of `p g` and of
`(τ k - 1 - X j * (φ k - 1) * (ε j)(φ k)) * g` for `g : G` and `k = (j, b)` (`IsTraceIdeal`); `ε j`
is `1` modulo `p` at the `ξ e (φ k)`. (4) For an element `a` of `G` and each `e`, the product of the
`ξ e a - ξ k a` over `k ≠ e` divides `C`; each `j` has a type `ty j`, monotone in `j`. (5) The
cocycles `c` of `ρ π` with values in `Frac(O) / O` that have `∑ θ g • c g = 0` whenever
`∑ θ g • (u x g - 1) = 0` for all `x` and vanish at the `τ k` and at `γ π` form a module of length
at most `b₀`. (6) The `δ v` are trivial on the characters and `o v * (X - 1)` kills every
`u x (δ v)`. (7) Every module `Z` of character cocycles for `ξ e` satisfies `HasTriangleCost` along
the `j` of type `e`, and a member of `Z` that vanishes on the finite set `s ⊆ G` is zero
(`IsDetectedBy`). Then the determinants of all combinations `∑ ω g (u x g - 1)` lie in `S` and
vanish on `𝓧`, one `f : S` multiplies them into `𝒥`, `f` has on `𝓧` no monomial properly dividing
`∏ X j`, and the coefficient of `∏ X j` in `f π` comes from some `c : O` of valuation at most
`b₀ + ∑ b e + t (∑ val (o v (1)) + 2 #s val C) + (#J + 1) val C`, with `val = addVal O` and `t` the
number of characters. -/
lemma exists_isCommonRibetElement_addVal_le (u : Y → G →* Matrix σ σ O)
    {S : Subalgebra O (Y → MvPolynomial J L)} (𝒥 : Submodule S (Y → MvPolynomial J L))
    [DVR O] [Fintype Y] [Fintype J] [LinearOrder J] {r : Type}
    [Fintype r] [DecidableEq r] {t : ℕ} [NeZero t] (blockEquiv : r ⊕ Fin t ≃ σ)
    -- (1) on `𝓧`, `u x` is the block `ρ x` plus the characters `ξ e`
    {𝓧 : Set Y} (π : 𝓧) (ρ : 𝓧 → G →* Matrix r r O) {ξ : Fin t → G →* O} (hξ₀ : ξ 0 = 1)
    (hu_block : ∀ (x : 𝓧) (g : G),
      u x g = reindex blockEquiv blockEquiv
        (fromBlocks (ρ x g) 0 0 (diagonal fun e : Fin t ↦ ξ e g)))
    (hρ_span : span O (Set.range (ρ π)) = ⊤)
    -- (2) `γ x` is a scalar `y x` on the block, `y x - 1` a unit, and trivial on the characters
    {γ : 𝓧 → G} {y : 𝓧 → O} (hργ : ∀ x : 𝓧, ρ x (γ x) = y x • 1)
    (hy_unit : ∀ x : 𝓧, IsUnit (y x - 1)) (hξγ : ∀ (x : 𝓧) (e : Fin t), ξ e (γ x) = 1)
    -- (3) two relations in `𝒥` for each `j : J`, indexed by `(j, true)` and `(j, false)`, whose
    -- factors `ε` are `1` modulo `p` on the characters
    {p : O} {τ φ : J × Bool → G} {ε : J → O[X]} (hp : p ≠ 0)
    (h𝒥 : IsTraceIdeal 𝒥 (fun x : Y ↦ u x) p τ φ Prod.fst ε)
    (hε : ∀ (e : Fin t) (k : J × Bool), p ∣ (ε k.1).eval (ξ e (φ k)) - 1)
    -- (4) `a` separates the characters up to `C`; `ty j` is the character that `j` belongs to
    (a : G) {C : O}
    (hC_dvd : ∀ e : Fin t, ∏ k ∈ ({e}ᶜ : Finset (Fin t)), (ξ e a - ξ k a) ∣ C) (ty : J →o Fin t)
    -- (5) the bound `b₀` for cocycles of the block with values in `K/O` that vanish at the `τ k`
    -- and at `γ π`
    {b₀ : ℕ}
    (hb₀ : length O (ribetCocyclesVanishingOn u (ρ π) (DivisibleQuot O) (Set.range τ) (γ π)) ≤ b₀)
    -- (6) elements `δ v`, trivial on the characters, with `u x (δ v)` killed by `o v * (X - 1)`
    [Fintype W] {δ : W → G} {o : W → O[X]} (hξδ : ∀ (v : W) (e : Fin t), ξ e (δ v) = 1)
    (hδ_poly : ∀ (v : W) (x : Y), aeval (u x (δ v)) (o v * (X - 1)) = 0)
    -- (7) a module `Z` of cocycles of `ξ e` modulo `p` costs at most `b e` and is detected by `s`
    {s : Finset G} {b : Fin t → ℕ∞}
    (hb : ∀ (e : Fin t) (Z : Submodule O (G → Unit → QuotSpan p)),
      (∀ c ∈ Z, IsCharacterCocycle u (ξ e) δ (γ π) a c) →
      HasTriangleCost Z (fun j : J ↦ τ (j, true)) (fun j : J ↦ τ (j, false))
          (fun j : J ↦ φ (j, true)) (fun j : J ↦ φ (j, false)) {j : J | ty j = e} C (b e) ∧
        IsDetectedBy Z s) :
    ∃ c : O,
      -- (a) `c` is the coefficient of `∏ X j` at `π` in one Ribet element for every `ω`
      IsCommonRibetElement 𝒥
        (fun (ω : G →₀ O) (x : Y) ↦
          algebraMap O L (linearCombination O (fun g : G ↦ u x g - 1) ω).det)
        π (algebraMap O L c) ∧
      -- (b) its valuation is at most the bounds `b₀`, `b e` plus the loss
      addVal O c ≤ b₀ + (∑ e : Fin t, b e +
        t * (∑ v : W, addVal O (eval 1 (o v)) + 2 * #s * addVal O C) +
        (Fintype.card J + 1) * addVal O C) := by
  classical
  obtain ⟨k, hkξ, hkρ⟩ := exists_character_projector ρ hργ hy_unit hξγ
  have exists_q (e : Fin t) : ∃ q : (MvPolynomial J O)[G],
      ∀ e' : Fin t, polyChar J (ξ e') q = if e' = e then .C C else 0 := by
    refine exists_apply_eq_ite_of_prod_dvd (fun e' ↦ polyChar J (ξ e')) (.single a 1) ?_
    simpa [polyChar_single] using map_dvd (MvPolynomial.C (σ := J)) (hC_dvd e)
  choose q hq using exists_q
  obtain ⟨s₀, z, hz⟩ := exists_areCoordinates_ribetGenerators u δ s
  obtain ⟨c₁, hc₁⟩ : ∃ c : O, c * (y π - 1) = 1 := (hy_unit π).exists_left_inv
  let T : TieSystem O Y G J σ := ⟨u, p, τ, φ, ε, tiedNormaliser J (γ π) a c₁⟩
  obtain ⟨B₀, hB₀, hB₀_val⟩ := T.exists_tiedRows_addVal_det_le (ρ π) hρ_span (hργ π) hc₁ rfl hz hb₀
  obtain ⟨n, wt, M, hM, hQ⟩ :=
    T.exists_characterRows hξδ hδ_poly hz (hξγ π) rfl hp hε hq ty hb
  obtain ⟨Q, hQ_coeff, hQ_val⟩ := hQ
  have hη₀ : polyChar J (ξ 0) T.ρ₀ = 0 := by
    simp [T, tiedNormaliser, polyChar_single, hξ₀, AlgHom.map_smul_of_tower]
  obtain ⟨h_det_mem, f, hf_mem, hf_val⟩ :=
    exists_traceIdeal_multiplier_eq_sum_det 𝒥 T blockEquiv ρ hu_block h𝒥 hz hkξ hkρ (hq 0) hη₀
      B₀ hB₀ wt M hM
  let D (x : 𝓧) : MvPolynomial J O :=
    (Matrix.comp _ _ r r (MvPolynomial J O) (B₀.map (polyAction J (ρ x)))).det
  have hf_coeff (x : 𝓧) (i : J →₀ ℕ) (hi : i ≤ ∑ j : J, .single j 1) :
      (f.val x).coeff i = algebraMap O L
        (if ∑ j, .single j 1 = i then MvPolynomial.constantCoeff (MvPolynomial.C C * D x * Q)
          else 0) := by
    rw [hf_val x, MvPolynomial.coeff_map, ← hQ_coeff (MvPolynomial.C C * D x) hi]
    congr 1
    simp only [D, Finset.mul_sum, mul_left_comm (wt _)]
  refine ⟨MvPolynomial.constantCoeff (MvPolynomial.C C * D π * Q),
    ⟨h_det_mem, fun ω x ↦ ?_, f, hf_mem, fun x i hi ↦ ?_, ?_⟩, ?_⟩
  · simp only [det_linearCombination_sub_one_eq_zero u blockEquiv hξ₀ (hu_block x), map_zero]
  · rw [hf_coeff x i hi.le, ite_eq_right hi.ne', map_zero]
  · rw [hf_coeff π _ le_rfl, ite_eq_left rfl]
  · have hD_eq : MvPolynomial.constantCoeff (D π) =
        (Matrix.comp _ _ r r O (B₀.map (polyActionAtZero J (ρ π)))).det := by
      simp [D, polyActionAtZero, det_apply']
    have hD : addVal O (MvPolynomial.constantCoeff (D π)) ≤ b₀ := by rwa [hD_eq]
    calc addVal O (MvPolynomial.constantCoeff (MvPolynomial.C C * D π * Q))
        = addVal O C + addVal O (MvPolynomial.constantCoeff (D π)) +
            addVal O (MvPolynomial.constantCoeff Q) := by
          simp only [map_mul, MvPolynomial.constantCoeff_C, addVal_mul]
      _ ≤ addVal O C + b₀ + (∑ e, b e +
            t * (∑ v, addVal O (eval 1 (o v)) + 2 * #s * addVal O C) +
            Fintype.card J * addVal O C) := add_le_add (add_le_add le_rfl hD) hQ_val
      _ = b₀ + (∑ e, b e + t * (∑ v, addVal O (eval 1 (o v)) + 2 * #s * addVal O C) +
            (Fintype.card J + 1) * addVal O C) := by ring

end Lemma

end New.Selmer

end RibetFirstOrder
