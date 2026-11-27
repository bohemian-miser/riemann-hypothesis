module

import Mathlib.GroupTheory.IndexNSmul
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
public import Lib.Weil.Construction.ThetaDictionary
public import Lib.General.Algebra.AdicCompletion
import Lib.Adelic.Adeles.StrongApproximation
import Lib.Cohomology.Etale.Basic

/-!
# Fourier inversion for theta functions

Let `δ` be integral with `δ δ̄` a nonzero natural number and let `r` be the number of elements of
`InfinitePlace E × n`, that is, the number of infinite places times the rank.

* `New.Space.exists_entireTheta_eq_of_isThetaFunction`: a theta function for `δ̄ 𝔞₀ⁿ` is the theta
  function of a vector `φ` of the finite part `V.finitePart` (a subspace containing the vacuum and
  stable under the translations `V.ϱ (finVec _)`).
* `New.Space.fourier_inversion`: if the theta function of `φ` is one for `δ̄ 𝔞₀ⁿ` and `y` runs over
  `δ⁻¹ 𝔞₀ⁿ⧸𝔞₀ⁿ`, the signed sums of translates of `ρ(-y) φ` over `𝔞₀ⁿ⧸δ̄ 𝔞₀ⁿ` are multiples
  `c_y vac` of the vacuum, and `∑ c_y ρ(y) vac = (δ δ̄) ^ r φ`, with `ρ` the finite translation.
* `New.Space.norm_mul_vacElem_le_one_of_eq_sum`: if the values of `φ` at the vectors `finVec x` are
  integral at a prime, then so are those of such a multiple `c_y vac`.

Here `φ` lies in `𝒮 V`. In the first two results the space `V` is standard (`V.IsStd`: all signs are
`+1` and the point is the identity); the third holds for every space. The theta functions of these
sums are theta functions for `𝔞₀ⁿ`, and orthogonality of the characters of `δ⁻¹ 𝔞₀ⁿ⧸𝔞₀ⁿ` inverts the
summation.

Notions from other files:
* `idealLattice E n` is the lattice `𝔞₀ⁿ` in `Eⁿ` of the vectors with integral finite image
  `finiteImage`, and `Ô E` is the ring of integral finite adeles.
* `ratShift γ` is the translation `T_γ` of functions on `ℂ^(InfinitePlace E × n)`, `ratPhase γ γ'`
  the commutator of `T_γ` and `T_γ'`, and `signedShift γ` the translation `T_γ` times the
  semicharacter at `γ`.
* `IsThetaFunction Y F` says that `F` is entire and fixed by the signed translations along `Y`.
* `entireTheta φ` is the theta function of a vector `φ` of `𝒮 V`. The vector `V.vacElem` is the
  vacuum, `V.ϱ` the translation by adelic vectors and `V.finHeisenbergOp` the signed finite
  translation.

## Relation to the literature

Known result: theta functions for a sublattice are spanned by translates of the theta function of a
principal polarization. The proof is by Fourier inversion on a finite abelian group. Source:
Mumford, Tata lectures on theta I.
-/

@[expose] public section

open NumberField Complex ComplexConjugate Pointwise

namespace New

open WeilData stdLattice Space

/-- The chosen representative of a class of `K ⧸ H ⊓ K` lies in `H` precisely for the zero
class. -/
@[simp] lemma coe_out_mem_iff {A : Type} [AddCommGroup A] {K H : AddSubgroup A}
    {q : K ⧸ H.addSubgroupOf K} : (q.out : A) ∈ H ↔ q = 0 := by
  rw [← AddSubgroup.mem_addSubgroupOf, ← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']

open Classical in
/-- Orthogonality: for `ψ` multiplicative and trivial on `H`, the sum of `ψ` over chosen
representatives of `K ⧸ H ⊓ K` is `[K : H ⊓ K]` if `ψ` is trivial on `K`, and `0` otherwise. -/
lemma sum_quotient_out_eq_ite {A : Type} [AddCommGroup A] {K H : AddSubgroup A}
    [Fintype (K ⧸ H.addSubgroupOf K)] {ψ : A → ℂ}
    (h_add : ∀ x x' : A, ψ (x + x') = ψ x * ψ x') (h_triv : ∀ x ∈ H, ψ x = 1) :
    ∑ q : K ⧸ H.addSubgroupOf K, ψ (q.out : A) =
      if ∀ x ∈ K, ψ x = 1 then (Fintype.card (K ⧸ H.addSubgroupOf K) : ℂ) else 0 := by
  let φ : K →+ Additive ℂ :=
    { toFun x := .ofMul (ψ x), map_zero' := h_triv 0 (zero_mem H), map_add' x y := h_add x y }
  let χ : AddChar (K ⧸ H.addSubgroupOf K) ℂ := AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (H.addSubgroupOf K) φ fun x hx ↦ h_triv x hx)
  have hχ : ∀ q, ψ (q.out : A) = χ q := fun q ↦ congrArg χ (QuotientAddGroup.out_eq' q)
  have h_zero : χ = 0 ↔ ∀ x ∈ K, ψ x = 1 :=
    AddChar.eq_zero_iff.trans (QuotientAddGroup.forall_mk.trans Subtype.forall)
  simpa only [hχ, h_zero] using χ.sum_eq_ite

/-- The index of `N L` in a free `ℤ`-module `L` of finite rank `r` is `N ^ r`. -/
lemma relIndex_map_nsmul_toAddSubgroup {M : Type} [AddCommGroup M] (N : ℕ) (L : Submodule ℤ M)
    [Module.Free ℤ L] [Module.Finite ℤ L] :
    (L.toAddSubgroup.map (nsmulAddMonoidHom N)).relIndex L.toAddSubgroup =
      N ^ Module.finrank ℤ L := by
  rw [AddSubgroup.relIndex, AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range]
  exact AddSubgroup.index_range_nsmul L N

/-- The quotient group `δ⁻¹ 𝔞₀ⁿ⧸𝔞₀ⁿ`, where `𝔞₀ⁿ = idealLattice E n`. -/
abbrev invSmulQuotient (E n : Type) [Field E] [CMType E] [WeilData E] (δ : E) : Type :=
  ↥(δ⁻¹ • idealLattice E n) ⧸ (idealLattice E n).addSubgroupOf (δ⁻¹ • idealLattice E n)

/-- The quotient group `𝔞₀ⁿ⧸δ̄ 𝔞₀ⁿ`, where `𝔞₀ⁿ = idealLattice E n`. -/
abbrev starSmulQuotient (E n : Type) [Field E] [CMType E] [WeilData E] (δ : E) : Type :=
  ↥(idealLattice E n) ⧸ (star δ • idealLattice E n).addSubgroupOf (idealLattice E n)

variable {E n : Type} [Field E] [CMType E] [WeilData E] [Fintype n]
  {F : (InfinitePlace E × n → ℂ) → ℂ} {δ : E} {N : ℕ}

lemma ratShift_neg_ratShift (y : n → E) : ratShift (-y) (ratShift y F) = F := by
  simp [ratShift_ratShift, ratRiemannForm, realImage_neg, ratShift_zero]

/-- The commutator `exp (2 π i {y, γ})`, with `{·,·}` the Riemann form `ratRiemannForm`, is
`exp (2 π i {-γ, y})`, as the Riemann form is alternating. -/
lemma ratPhase_swap (γ y : n → E) : ratPhase y γ = ratPhase (-γ) y := by
  rw [ratPhase, ratRiemannForm_swap γ y]
  simp [ratPhase, ratRiemannForm, realImage_neg]

/-- A translate `T_y F = ratShift y F` of a theta function for `Y` is one too if `T_y` commutes with
the translations along `Y`, that is, if the commutator `ratPhase γ y` is `1` for `γ ∈ Y`. -/
lemma IsThetaFunction.ratShift {Y : AddSubgroup (n → E)} (hF : IsThetaFunction Y F) {y : n → E}
    (hy : ∀ γ ∈ Y, ratPhase γ y = 1) : IsThetaFunction Y (ratShift y F) := by
  refine ⟨differentiable_thetaShift _ _ hF.differentiable, fun γ hγ ↦ ?_⟩
  rw [signedShift_apply, ratShift_comm, hy γ hγ, one_smul, ← map_smul, ← signedShift_apply,
    hF.signedShift_eq γ hγ]

/-- Let `F` be a theta function for `Y` and let `Y ⊓ 𝔞₀ⁿ` have finite index in `𝔞₀ⁿ`. Then the sum
over `q` in `𝔞₀ⁿ⧸(Y ⊓ 𝔞₀ⁿ)` of the signed translates `signedShift (-q.out) F` is one for `𝔞₀ⁿ`. -/
lemma IsThetaFunction.sum_signedShift [DecidableEq n] {Y : AddSubgroup (n → E)}
    [Fintype (idealLattice E n ⧸ Y.addSubgroupOf (idealLattice E n))] (hF : IsThetaFunction Y F) :
    IsThetaFunction (idealLattice E n)
      (∑ q : idealLattice E n ⧸ Y.addSubgroupOf (idealLattice E n),
        signedShift (-q.out.val) F) := by
  refine ⟨.sum fun q _ ↦ ?_, fun a ha ↦ ?_⟩
  · rw [signedShift_apply]
    exact (differentiable_thetaShift _ _ hF.differentiable).const_smul _
  · rw [map_sum]
    refine Fintype.sum_equiv (.addLeft (QuotientAddGroup.mk ⟨-a, neg_mem ha⟩)) _ _ fun q ↦ ?_
    let q' := QuotientAddGroup.mk (s := Y.addSubgroupOf (idealLattice E n)) ⟨-a, neg_mem ha⟩ + q
    have h_mem : q'.out.val - (-a + q.out.val) ∈ Y := by
      change ((q'.out - (⟨-a, neg_mem ha⟩ + q.out) : idealLattice E n) : n → E) ∈ Y
      rw [← AddSubgroup.mem_addSubgroupOf, ← QuotientAddGroup.eq_iff_sub_mem,
        QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
    change signedShift a (signedShift (-q.out.val) F) = signedShift (-q'.out.val) F
    rw [← signedShift_add ha (neg_mem q.out.property),
      show -q'.out.val = (a + -q.out.val) + -(q'.out.val - (-a + q.out.val)) by abel,
      signedShift_add (add_mem ha (neg_mem q.out.property))
        (neg_mem (sub_mem q'.out.property (add_mem (neg_mem ha) q.out.property))),
      hF.signedShift_eq _ (neg_mem h_mem)]

omit [WeilData E] in
lemma ne_zero_of_mul_star_eq (hN_ne : N ≠ 0) (hN : δ * star δ = N) : δ ≠ 0 :=
  fun h_zero ↦ hN_ne (by simpa [h_zero] using hN.symm)

section

omit [Fintype n]

/-- For an integral `δ` the lattice `δ̄ 𝔞₀ⁿ` lies in `𝔞₀ⁿ`. -/
lemma star_smul_idealLattice_le (hδ : (δ : 𝔸f E) ∈ Ô E) :
    star δ • idealLattice E n ≤ idealLattice E n := by
  rintro - ⟨γ, hγ, rfl⟩
  exact smul_mem_idealLattice (by simpa using star_mem_Ô hδ) hγ

/-- For a nonzero integral `δ` the lattice `𝔞₀ⁿ` lies in `δ⁻¹ 𝔞₀ⁿ`. -/
lemma idealLattice_le_inv_smul (hδ : (δ : 𝔸f E) ∈ Ô E) (hδ_ne : δ ≠ 0) :
    idealLattice E n ≤ δ⁻¹ • idealLattice E n :=
  fun _ hγ ↦ (mem_inv_smul_idealLattice hδ_ne).2 (smul_mem_idealLattice hδ hγ)

/-- For `δ δ̄ = N` and `δ ≠ 0`, the index of `δ̄ 𝔞₀ⁿ` in `δ⁻¹ 𝔞₀ⁿ` is that of `N 𝔞₀ⁿ` in `𝔞₀ⁿ`,
where `𝔞₀ⁿ = idealLattice E n`: multiplication by `δ` carries one pair to the other. -/
lemma relIndex_star_smul_inv_smul (hδ_ne : δ ≠ 0) (hN : δ * star δ = N) :
    (star δ • idealLattice E n).relIndex (δ⁻¹ • idealLattice E n) =
      ((idealLattice E n).map (nsmulAddMonoidHom N)).relIndex (idealLattice E n) := by
  have h_small : δ • star δ • idealLattice E n = (idealLattice E n).map (nsmulAddMonoidHom N) := by
    ext x
    simp [smul_smul, hN, AddSubgroup.pointwise_smul_def, Nat.cast_smul_eq_nsmul]
  calc _ = (δ • star δ • idealLattice E n).relIndex (δ • δ⁻¹ • idealLattice E n) :=
        (AddSubgroup.relIndex_map_map_of_injective (f := DistribSMul.toAddMonoidHom (n → E) δ)
          _ _ (smul_right_injective _ hδ_ne)).symm
    _ = _ := by rw [h_small, smul_inv_smul₀ hδ_ne]

end

variable [DecidableEq n]

/-- The index of `N 𝔞₀ⁿ` in the lattice `𝔞₀ⁿ = idealLattice E n` is `N ^ (2 r)`, with `r` the number
of elements of `InfinitePlace E × n`: the real image `realLattice E n` of `𝔞₀ⁿ` is a lattice of
rank `2 r`. -/
lemma relIndex_map_nsmul_idealLattice (N : ℕ) :
    ((idealLattice E n).map (nsmulAddMonoidHom N)).relIndex (idealLattice E n) =
      N ^ (2 * Fintype.card (InfinitePlace E × n)) := by
  have h_rank : Module.finrank ℤ (realLattice E n) = 2 * Fintype.card (InfinitePlace E × n) := by
    rw [ZLattice.rank ℝ, finrank_real_of_complex, Module.finrank_fintype_fun_eq_card]
  have h_lattice : (realLattice E n).toAddSubgroup = (idealLattice E n).map realImageHom := rfl
  have h_real : ((idealLattice E n).map (nsmulAddMonoidHom N)).map realImageHom =
      (realLattice E n).toAddSubgroup.map (nsmulAddMonoidHom N) := by
    ext x
    -- `nsmul_eq_mul` is left out, so that `map_nsmul` applies
    simp [h_lattice, -nsmul_eq_mul, map_nsmul]
  rw [← AddSubgroup.relIndex_map_map_of_injective _ _ injective_realImageHom, h_real, ← h_lattice,
    relIndex_map_nsmul_toAddSubgroup, h_rank]

/-- For `δ` integral with `δ δ̄ = N ≠ 0`, the orders of `𝔞₀ⁿ⧸δ̄ 𝔞₀ⁿ` and `δ⁻¹ 𝔞₀ⁿ⧸𝔞₀ⁿ` have the
product `N ^ (2 r)`, with `r` the number of elements of `InfinitePlace E × n`. -/
lemma relIndex_mul_relIndex_idealLattice (hδ : (δ : 𝔸f E) ∈ Ô E) (hN_ne : N ≠ 0)
    (hN : δ * star δ = N) :
    (star δ • idealLattice E n).relIndex (idealLattice E n) *
      (idealLattice E n).relIndex (δ⁻¹ • idealLattice E n) =
        N ^ (2 * Fintype.card (InfinitePlace E × n)) := by
  have hδ_ne : δ ≠ 0 := ne_zero_of_mul_star_eq hN_ne hN
  rw [AddSubgroup.relIndex_mul_relIndex _ _ _ (star_smul_idealLattice_le hδ)
    (idealLattice_le_inv_smul hδ hδ_ne), relIndex_star_smul_inv_smul hδ_ne hN,
    relIndex_map_nsmul_idealLattice]

section Inversion

open Classical in
/-- Let `δ ≠ 0` and `𝔞₀ⁿ = idealLattice E n`. For `x` in `𝔞₀ⁿ`, the sum of the commutators
`ratPhase x y = exp (2 π i {x, y})` over representatives `y` of `δ⁻¹ 𝔞₀ⁿ` modulo `𝔞₀ⁿ` is their
number if `x` lies in `δ̄ 𝔞₀ⁿ`, and `0` otherwise. -/
lemma sum_ratPhase_inv_smul [Fintype (invSmulQuotient E n δ)] (hδ_ne : δ ≠ 0) {x : n → E}
    (hx : x ∈ idealLattice E n) :
    ∑ y : invSmulQuotient E n δ, ratPhase x y.out =
      if x ∈ star δ • idealLattice E n then (Fintype.card (invSmulQuotient E n δ) : ℂ) else 0 := by
  rw [sum_quotient_out_eq_ite (ratPhase_add_right x) (mem_idealLattice_iff_ratPhase.1 hx)]
  simp only [mem_star_smul_idealLattice_iff hδ_ne]

open Classical in
/-- Let `δ ≠ 0` and `𝔞₀ⁿ = idealLattice E n`. For `x` in `δ⁻¹ 𝔞₀ⁿ`, the sum of the commutators
`ratPhase γ x = exp (2 π i {γ, x})` over representatives `γ` of `𝔞₀ⁿ` modulo `δ̄ 𝔞₀ⁿ` is their
number if `x` lies in `𝔞₀ⁿ`, and `0` otherwise. -/
lemma sum_ratPhase_star_smul [Fintype (starSmulQuotient E n δ)] (hδ_ne : δ ≠ 0) {x : n → E}
    (hx : x ∈ δ⁻¹ • idealLattice E n) :
    ∑ γ : starSmulQuotient E n δ, ratPhase γ.out x =
      if x ∈ idealLattice E n then (Fintype.card (starSmulQuotient E n δ) : ℂ) else 0 := by
  have h_triv : ∀ z ∈ star δ • idealLattice E n, ratPhase z x = 1 :=
    fun z hz ↦ (mem_star_smul_idealLattice_iff hδ_ne).1 hz x hx
  rw [sum_quotient_out_eq_ite (ψ := (ratPhase · x)) (fun z z' ↦ ratPhase_add_left z z' x) h_triv]
  -- `ratPhase z x = ratPhase (-x) z`, and `𝔞₀ⁿ` is its own dual.
  simp only [ratPhase_swap x, ← mem_idealLattice_iff_ratPhase, neg_mem_iff]

variable [Fintype (invSmulQuotient E n δ)] [Fintype (starSmulQuotient E n δ)]

/-- For `δ ≠ 0` and `𝔞₀ⁿ = idealLattice E n`, there are as many classes of `δ⁻¹ 𝔞₀ⁿ` modulo `𝔞₀ⁿ`
as of `𝔞₀ⁿ` modulo `δ̄ 𝔞₀ⁿ`, as the commutator pairing makes them dual to each other. -/
lemma card_representatives_inv_smul_eq_card_star_smul (hδ_ne : δ ≠ 0) :
    Fintype.card (invSmulQuotient E n δ) = Fintype.card (starSmulQuotient E n δ) := by
  -- Both cardinalities are the double sum of the pairing, taken in the two orders of summation.
  classical
  have h_left : ∑ γ : starSmulQuotient E n δ, ∑ y : invSmulQuotient E n δ,
      ratPhase γ.out.val y.out = Fintype.card (invSmulQuotient E n δ) := by
    simp [fun γ : starSmulQuotient E n δ ↦ sum_ratPhase_inv_smul hδ_ne γ.out.property]
  have h_right : ∑ y : invSmulQuotient E n δ, ∑ γ : starSmulQuotient E n δ,
      ratPhase γ.out.val y.out = Fintype.card (starSmulQuotient E n δ) := by
    simp [fun y : invSmulQuotient E n δ ↦ sum_ratPhase_star_smul hδ_ne y.out.property]
  exact_mod_cast h_left.symm.trans (Finset.sum_comm.trans h_right)

/-- For `δ` integral with `δ δ̄ = N ≠ 0` and `𝔞₀ⁿ = idealLattice E n`, the representatives `y` of
`δ⁻¹ 𝔞₀ⁿ⧸𝔞₀ⁿ` and `γ` of `𝔞₀ⁿ⧸δ̄ 𝔞₀ⁿ` both number `N ^ r`, with `r` the number of elements of
`InfinitePlace E × n`. -/
lemma card_representatives_idealLattice (hδ : (δ : 𝔸f E) ∈ Ô E) (hN_ne : N ≠ 0)
    (hN : δ * star δ = N) :
    Fintype.card (invSmulQuotient E n δ) = N ^ Fintype.card (InfinitePlace E × n) ∧
      Fintype.card (starSmulQuotient E n δ) = N ^ Fintype.card (InfinitePlace E × n) := by
  -- The two orders are equal and their product is `N ^ (2 r)`.
  have h_eq : Fintype.card (invSmulQuotient E n δ) = Fintype.card (starSmulQuotient E n δ) :=
    card_representatives_inv_smul_eq_card_star_smul (ne_zero_of_mul_star_eq hN_ne hN)
  have h_mul : Fintype.card (starSmulQuotient E n δ) * Fintype.card (invSmulQuotient E n δ) =
      N ^ (2 * Fintype.card (InfinitePlace E × n)) := by
    simpa only [Fintype.card_eq_nat_card, ← AddSubgroup.index_eq_card, AddSubgroup.relIndex] using
      relIndex_mul_relIndex_idealLattice (n := n) hδ hN_ne hN
  have h_card : Fintype.card (starSmulQuotient E n δ) = N ^ Fintype.card (InfinitePlace E × n) :=
    Nat.mul_self_inj.1 (by rw [← pow_add, ← two_mul, ← h_mul, h_eq])
  exact ⟨h_eq.trans h_card, h_card⟩

/-- Let `F` be a theta function (entire, fixed by the signed translations) for `δ̄ 𝔞₀ⁿ`, `δ ≠ 0`,
with `𝔞₀ⁿ = idealLattice E n`, and let `y`, `γ` run over representatives of `δ⁻¹ 𝔞₀ⁿ⧸𝔞₀ⁿ` and
`𝔞₀ⁿ⧸δ̄ 𝔞₀ⁿ`. With `T_y = ratShift y` the translation and `S_γ = signedShift γ` the signed
translation, `∑_y T_(-y) ∑_γ S_(-γ) T_y F` is `F` times the number of the `y`. -/
lemma IsThetaFunction.sum_ratShift_sum_signedShift (hδ_ne : δ ≠ 0)
    (hF : IsThetaFunction (star δ • idealLattice E n) F) :
    ∑ y : invSmulQuotient E n δ, New.ratShift (-y.out.val)
      (∑ γ : starSmulQuotient E n δ, signedShift (-γ.out.val) (New.ratShift y.out.val F)) =
      (Fintype.card (invSmulQuotient E n δ) : ℂ) • F := by
  -- Conjugating `S_(-γ)` by `T_y` multiplies it by a character of `y`; summing over `y` leaves
  -- only the `γ` in `δ̄ 𝔞₀ⁿ`.
  classical
  have h_conj (x z : n → E) :
      New.ratShift (-z) (signedShift x (New.ratShift z F)) = ratPhase x z • signedShift x F := by
    rw [signedShift_apply, ratShift_comm x, map_smul, map_smul, ratShift_neg_ratShift,
      signedShift_apply, smul_comm]
  calc _ = ∑ γ : starSmulQuotient E n δ,
        (∑ y : invSmulQuotient E n δ, ratPhase (-γ.out.val) y.out.val) •
          signedShift (-γ.out.val) F := by
        simpa only [map_sum, h_conj, Finset.sum_smul] using Finset.sum_comm
    _ = (Fintype.card (invSmulQuotient E n δ) : ℂ) •
        signedShift (-(0 : starSmulQuotient E n δ).out.val) F := by
        simp [fun γ : starSmulQuotient E n δ ↦ sum_ratPhase_inv_smul hδ_ne (neg_mem γ.out.property)]
    _ = (Fintype.card (invSmulQuotient E n δ) : ℂ) • F := by
        rw [hF.signedShift_eq _ (neg_mem (coe_out_mem_iff.2 rfl))]

/-- Fourier inversion for theta functions in a standard space `V` (all signs are `+1`, the point is
the identity). Let `δ` be integral with `δ δ̄ = N ≠ 0` and `F` a theta function for `δ̄ 𝔞₀ⁿ`, where
`𝔞₀ⁿ = idealLattice E n`: `F` is entire and fixed by the signed translations `signedShift` along
`δ̄ 𝔞₀ⁿ`. Let `y`, `γ` represent `δ⁻¹ 𝔞₀ⁿ⧸𝔞₀ⁿ` and `𝔞₀ⁿ⧸δ̄ 𝔞₀ⁿ`. With `T_y = ratShift y`, the sum
of the `signedShift (-γ) (T_y F)` is a multiple `c_y ϑ` of the theta function `ϑ` of the vacuum, and
`∑ c_y T_(-y) ϑ = N ^ r F`, with `r` the number of elements of `InfinitePlace E × n`. -/
lemma Space.exists_smul_entireTheta_vacElem_eq {ε : n → ℤˣ} (V : Space E n ε) [V.IsStd]
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN_ne : N ≠ 0) (hN : δ * star δ = N)
    (hF : IsThetaFunction (star δ • idealLattice E n) F) :
    ∃ c : invSmulQuotient E n δ → ℂ,
      (∀ y, c y • entireTheta V.vacElem =
        ∑ γ : starSmulQuotient E n δ, signedShift (-γ.out.val) (ratShift y.out.val F)) ∧
      ∑ y, c y • ratShift (-y.out.val) (entireTheta V.vacElem) =
        (N : ℂ) ^ Fintype.card (InfinitePlace E × n) • F := by
  have hδ_ne : δ ≠ 0 := ne_zero_of_mul_star_eq hN_ne hN
  have h_multiple (y : invSmulQuotient E n δ) : ∃ c : ℂ, c • entireTheta V.vacElem =
      ∑ γ : starSmulQuotient E n δ, signedShift (-γ.out.val) (ratShift y.out.val F) := by
    have h_phase : ∀ x ∈ star δ • idealLattice E n, ratPhase x y.out.val = 1 :=
      fun x hx ↦ (mem_star_smul_idealLattice_iff hδ_ne).1 hx _ y.out.property
    exact V.exists_smul_entireTheta_of_isThetaFunction (hF.ratShift h_phase).sum_signedShift
  choose c hc using h_multiple
  refine ⟨c, hc, ?_⟩
  calc _ = ∑ y : invSmulQuotient E n δ, ratShift (-y.out.val)
        (∑ γ : starSmulQuotient E n δ, signedShift (-γ.out.val) (ratShift y.out.val F)) := by
        simp only [← map_smul, hc]
    _ = (Fintype.card (invSmulQuotient E n δ) : ℂ) • F := hF.sum_ratShift_sum_signedShift hδ_ne
    _ = (N : ℂ) ^ Fintype.card (InfinitePlace E × n) • F := by
        rw [(card_representatives_idealLattice (n := n) hδ hN_ne hN).1, Nat.cast_pow]

/-- Fourier inversion in a standard space `V` (all signs are `+1`, the point is the identity). Let
`δ` be integral with `δ δ̄ = N ≠ 0` and let the theta function `entireTheta φ` of a vector `φ` of
`𝒮 V` be entire and fixed by the signed translations along `δ̄ 𝔞₀ⁿ`, where `𝔞₀ⁿ = idealLattice E n`.
Let `y` run over `δ⁻¹ 𝔞₀ⁿ⧸𝔞₀ⁿ` and `γ` over `𝔞₀ⁿ⧸δ̄ 𝔞₀ⁿ`. Then the sum of the signed translates, by
`V.finHeisenbergOp`, of `ρ(-y) φ` by the `γ` is a multiple `c_y vac` of the vacuum, and
`∑ c_y ρ(y) vac = N ^ r φ`. Here `ρ(y)` is the translation `V.ϱ` by the adelic vector
`finVec (finiteImage y)`, with finite part `y` (as `finiteImage` divides by the finite idele `α`
and `finVec` multiplies by it) and infinite part zero, and `r` is the number of elements of
`InfinitePlace E × n`.

This is used instead of the upper bound in Frobenius's formula for the dimension of a space of
classical theta functions (the Pfaffian of the Riemann form), for the lattice `δ̄ 𝔞₀ⁿ` and theta
functions of the form `entireTheta φ` only. -/
theorem Space.fourier_inversion {ε : n → ℤˣ} (V : Space E n ε) [V.IsStd]
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN_ne : N ≠ 0) (hN : δ * star δ = N) {φ : 𝒮 V}
    (hφ : IsThetaFunction (star δ • idealLattice E n) (entireTheta φ)) :
    ∃ c : invSmulQuotient E n δ → ℂ,
      (∀ y, c y • V.vacElem = ∑ γ : starSmulQuotient E n δ,
        V.finHeisenbergOp (finiteImage γ.out.val) (V.ϱ (finVec (finiteImage (-y.out.val))) φ)) ∧
      ∑ y, c y • V.ϱ (finVec (finiteImage y.out.val)) V.vacElem =
        (N : ℂ) ^ Fintype.card (InfinitePlace E × n) • φ := by
  -- Both equations may be checked on theta functions, as `φ ↦ entireTheta φ` is injective.
  obtain ⟨c, h_average, h_inversion⟩ := V.exists_smul_entireTheta_vacElem_eq hδ hN_ne hN hφ
  refine ⟨c, fun y ↦ V.injective_entireThetaHom ?_, V.injective_entireThetaHom ?_⟩
  · simpa only [map_sum, map_smul, entireThetaHom_apply, entireTheta_finHeisenbergOp,
      entireTheta_rho, neg_neg] using h_average y
  · simpa only [map_sum, map_smul, entireThetaHom_apply, entireTheta_rho] using h_inversion

end Inversion

/-- Let `δ` be integral with `δ δ̄ = N ≠ 0` and let `V` be a standard space (all signs are `+1` and
the point is the identity). Every theta function `F` for the lattice
`δ̄ 𝔞₀ⁿ = star δ • idealLattice E n`, that is, every entire function fixed by the signed
translations along it, is the theta function `entireTheta φ` of a vector `φ` of the finite part
`V.finitePart` (a subspace containing the vacuum and stable under the translations `V.ϱ (finVec _)`)
of `𝒮 V`. -/
theorem Space.exists_entireTheta_eq_of_isThetaFunction {ε : n → ℤˣ} (V : Space E n ε) [V.IsStd]
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN_ne : N ≠ 0) (hN : δ * star δ = N)
    (hF : IsThetaFunction (star δ • idealLattice E n) F) :
    ∃ φ ∈ V.finitePart, entireTheta φ = F := by
  have h_ne := (relIndex_mul_relIndex_idealLattice (n := n) hδ hN_ne hN).trans_ne
    (pow_ne_zero _ hN_ne)
  let := AddSubgroup.fintypeOfIndexNeZero (right_ne_zero_of_mul h_ne)
  let := AddSubgroup.fintypeOfIndexNeZero (left_ne_zero_of_mul h_ne)
  obtain ⟨c, -, h_inversion⟩ := V.exists_smul_entireTheta_vacElem_eq hδ hN_ne hN hF
  refine ⟨((N : ℂ) ^ Fintype.card (InfinitePlace E × n))⁻¹ •
    ∑ y : invSmulQuotient E n δ, c y • V.ϱ (finVec (finiteImage y.out.val)) V.vacElem, ?_, ?_⟩
  · exact Submodule.smul_mem _ _ <| sum_mem fun y _ ↦
      Submodule.smul_mem _ _ (rho_finVec_mem_finitePart _ vacElem_mem_finitePart)
  · rw [← entireThetaHom_apply, map_smul, map_sum]
    simp [entireThetaHom_apply, entireTheta_rho, h_inversion, smul_smul, hN_ne]

/-- Let `V` be a standard space (all signs are `+1` and the point is the identity), let `δ` be
integral with `δ δ̄ = N ≠ 0`, and let the theta function `entireTheta φ` of `φ` be one for `δ̄ 𝔞₀ⁿ`
(fixed by the signed translations along it), where `𝔞₀ⁿ = idealLattice E n`. There are finite
families of `y` with `δ y ∈ 𝔞₀ⁿ` and, indexed by `N ^ r` elements, of `γ ∈ 𝔞₀ⁿ`, and numbers
`c_y`, such that `c_y vac` is the signed sum of the translates of `ρ(-y) φ` by the `γ`, and
`∑ c_y ρ(y) vac = N ^ r φ`. Here `r` is the number of elements of `InfinitePlace E × n`, `vac` the
vacuum `V.vacElem`, `ρ(y)` the translation `V.ϱ` by the vector `finVec (finiteImage y)` with
infinite part zero, and `V.finHeisenbergOp` the signed translation. -/
theorem Space.exists_fourier_coefficients {ε : n → ℤˣ} (V : Space E n ε) [V.IsStd]
    (hδ : (δ : 𝔸f E) ∈ Ô E) (hN_ne : N ≠ 0) (hN : δ * star δ = N) {φ : 𝒮 V}
    (hφ : IsThetaFunction (star δ • idealLattice E n) (entireTheta φ)) :
    ∃ (Y Γ : Type) (_ : Fintype Y) (_ : Fintype Γ) (y : Y → n → E) (γ : Γ → n → E) (c : Y → ℂ),
      (∀ i : Y, δ • y i ∈ idealLattice E n) ∧
      (∀ j : Γ, γ j ∈ idealLattice E n) ∧
      Fintype.card Γ = N ^ Fintype.card (InfinitePlace E × n) ∧
      (∀ i : Y, c i • V.vacElem =
        ∑ j : Γ, V.finHeisenbergOp (finiteImage (γ j)) (V.ϱ (finVec (finiteImage (-y i))) φ)) ∧
      ∑ i : Y, c i • V.ϱ (finVec (finiteImage (y i))) V.vacElem =
        (N : ℂ) ^ Fintype.card (InfinitePlace E × n) • φ := by
  have h_ne := (relIndex_mul_relIndex_idealLattice (n := n) hδ hN_ne hN).trans_ne
    (pow_ne_zero _ hN_ne)
  let := AddSubgroup.fintypeOfIndexNeZero (right_ne_zero_of_mul h_ne)
  let := AddSubgroup.fintypeOfIndexNeZero (left_ne_zero_of_mul h_ne)
  obtain ⟨c, h_average, h_inversion⟩ := V.fourier_inversion hδ hN_ne hN hφ
  exact ⟨invSmulQuotient E n δ, starSmulQuotient E n δ, inferInstance, inferInstance,
    fun y ↦ y.out, fun γ ↦ γ.out, c,
    fun y ↦ (mem_inv_smul_idealLattice (ne_zero_of_mul_star_eq hN_ne hN)).1 y.out.property,
    fun γ ↦ γ.out.property, (card_representatives_idealLattice (n := n) hδ hN_ne hN).2,
    h_average, h_inversion⟩

/-- Let `E` be a CM field with Weil data, `V : Space E n ε` a hermitian space, `φ` a vector of
`𝒮 V`, and `a j`, `b`, `x` finite adelic vectors. Write `ρ(b) φ = V.ϱ (finVec b) φ` for the
translate of `φ` by `finVec b`, the adelic vector with finite part `α b` and infinite part zero,
where `α` is the finite idele of the Weil data. The value at `finVec x` of the sum over `j` of the
operators `V.finHeisenbergOp (a j)` (scalar-twisted translates) applied to `ρ(b) φ` equals a sum
over `j` of values of `φ` at some vectors `finVec (z j)`, each multiplied by the value at some `w j`
of the finite-adelic character `selfDualAddChar`. -/
lemma Space.exists_sum_finHeisenbergOp_apply_eq {ε : n → ℤˣ} (V : Space E n ε) {J : Type}
    [Fintype J] (a : J → n → 𝔸f E) (b x : n → 𝔸f E) (φ : 𝒮 V) :
    ∃ (w : J → 𝔸f E) (z : J → n → 𝔸f E),
      (∑ j : J, V.finHeisenbergOp (a j) (V.ϱ (finVec b) φ)) (finVec x) =
        ∑ j : J, selfDualAddChar E (w j) * φ (finVec (z j)) := by
  -- Composing the translations gives one by `a j + b`, so `φ` is evaluated at `x + (a j + b)`, and
  -- the phases add up.
  let w (j : J) : 𝔸f E := traceOneAdele * half * star (a j) ⬝ᵥ a j +
    (half * star b ⬝ᵥ a j + half * star (a j + b) ⬝ᵥ x)
  have h_term (j : J) : V.finHeisenbergOp (a j) (V.ϱ (finVec b) φ) (finVec x) =
      selfDualAddChar E (w j) * φ (finVec (x + (a j + b))) := by
    rw [← theta_rho]
    simp only [w, finHeisenbergOp, semichar, _root_.smul_apply, map_smul,
      rho_finVec_rho_finVec,
      smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, theta_rho]
  refine ⟨w, fun j ↦ x + (a j + b), ?_⟩
  rw [← theta_rho]
  simp only [map_sum, theta_rho, h_term]

/-- Let the values of a vector `φ` of `𝒮 V` at the points `finVec x` with infinite part zero be
integral at `p`, that is, of norm at most `1` under the embedding `ιₚ : ℂ → ℂ_[p]` given by the
instance `PadicPlace p`. If a multiple `c • vac` of the vacuum `V.vacElem` is a sum of signed
translates `V.finHeisenbergOp (a j)` of the translate `V.ϱ (finVec b) φ`, then the values of
`c • vac` at these points are integral too. -/
lemma Space.norm_mul_vacElem_le_one_of_eq_sum {ε : n → ℤˣ} (V : Space E n ε) {p : ℕ}
    [Fact p.Prime] [PadicPlace p] {φ : 𝒮 V} (hφ : ∀ x : n → 𝔸f E, ‖ιₚ (φ (finVec x))‖ ≤ 1)
    {c : ℂ} {J : Type} [Fintype J] {a : J → n → 𝔸f E} {b : n → 𝔸f E}
    (hc : c • V.vacElem = ∑ j : J, V.finHeisenbergOp (a j) (V.ϱ (finVec b) φ)) (x : n → 𝔸f E) :
    ‖ιₚ (c * V.vacElem (finVec x))‖ ≤ 1 := by
  -- The value is a sum of values of `φ` times roots of unity.
  obtain ⟨w, z, h_sum⟩ := V.exists_sum_finHeisenbergOp_apply_eq a b x φ
  have h_root (j : J) : ‖ιₚ (selfDualAddChar E (w j))‖ = 1 :=
    ((ιₚ : ℂ →* ℂ_[p]).isOfFinOrder (isOfFinOrder_ψf _)).norm_eq_one
  rw [← V.smul_apply, hc, h_sum, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ ↦ ?_
  rw [map_mul, norm_mul, h_root j, one_mul]
  exact hφ (z j)

end New
