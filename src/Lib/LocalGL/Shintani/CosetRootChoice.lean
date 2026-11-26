module

public import Lib.GaloisRep.Hilbert90.TameActions
public import Lib.LocalGL.Green.HallAlgebra
import TauCeti.RepresentationTheory.CharacterTable.CyclicExtension
import TauCeti.RepresentationTheory.CharacterTable.Gallagher
import TauCeti.RepresentationTheory.Induction.Character

/-!
# Root choices in a coset, induction, and extension of invariant characters

This file treats descent of class functions along a coset, as in Shintani descent. Given
`π : E →* Γ`, `σ ∈ Γ` and `j : G → E`, it defines root choices over `σ`. It defines the induction
`New.induceClassFn` of class functions along an injective homomorphism via `Subgroup.indClassFun`
and proves that it preserves combinations of characters. It proves that
descent keeps inner products and commutes with induction. It also proves the following for a
`Γ`-invariant irreducible character `Y` of `G` across a cyclic group `Γ` and a virtual character
`Φ` of `G ⋊ Γ` with |Γ|⟨Φ,Φ⟩ = ⟨Φ|G,Φ|G⟩+|Γ|−1 and ⟨Y,Φ|G⟩ = 1+|Γ|m for some m ∈ ℤ. Under these
conditions, the function equal to `Y` on `G` and to `Φ` off `G` is a character of `G ⋊ Γ`
(`New.IsIrreducibleChar.isChar_extend_semidirect`), obtained from Clifford extension across a
cyclic quotient and Gallagher's correspondence. Here `New.classInner` is the mean of `conj f * h`,
and `New.virtualChars` is the span of the characters.

## Main definitions and results

* `New.DescendsOnCoset`: the function `h` on `E` descends to `f` on `G` over the coset of `σ`:
  `h s = f γ` for every `s : E` with `π s = σ` and every `γ : G` with `s ^ orderOf σ = j γ`.
* `New.IsRootChoice`, `New.exists_isRootChoice`: a conjugation-equivariant choice, for each `γ`, of
  a root `r γ` over `σ` with `r γ ^ orderOf σ = j γ`, and its existence for the units of an algebra
  over a finite field with a semilinear Galois action.
* `New.IsRootChoice.exists_conj_eq_of_map_eq`, `New.IsRootChoice.index_mul_finMean_eq_classInner`:
  the roots meet every class over `σ`, and descent keeps inner products.
* `New.IsRootChoice.descendsOnCoset_comp`: a function `g` invariant under the kernel of `π` descends
  to `g ∘ r`.
* `New.induceClassFn_mem_virtualChars`: `New.induceClassFn` preserves `Z`-linear combinations of
  characters.
* `New.DescendsOnCoset.induce`: descent commutes with induction.

Notions from other files:
* `New.IsIrreducibleChar`: `f` is an irreducible character, stated as three conditions: (a) `f` is a
  character, (b) `New.classInner f f = 1`, and (c) for every class function `h` and every `y`, `f 1
  * New.classInner f (h (· * y)) = New.classInner f h * f y`.

## Relation to the literature

Known; see `Lib.LocalGL.Shintani.LiftingGreenCharacters` and `Lib.LocalGL.Green.CuspidalFunctions`
for sources.
-/

@[expose] public section

namespace New

section CosetRoots

open Finset Function Subgroup ComplexConjugate SemidirectProduct AddMonoidAlgebra
  ZMod

variable {E E' Γ G G' : Type*} [Group E] [Group E'] [Group Γ] [Group G] [Group G'] [Finite E]
  [Finite E'] [Finite G] [Finite G'] (π : E →* Γ) (σ : Γ)

/-- The function `h` on `E` descends to `f` on `G` over the coset of `σ`: `h s = f γ` for every
`s : E` with `π s = σ` and every `γ : G` with `s ^ orderOf σ = j γ`. -/
def DescendsOnCoset (j : G → E) (h : E → ℂ) (f : G → ℂ) : Prop :=
  ∀ (s : E) (γ : G), π s = σ → s ^ orderOf σ = j γ → h s = f γ

open scoped Classical in
/-- The number of x in the kernel of π with xtx⁻¹ = s, as a complex number. -/
noncomputable def conjCount (s t : E) : ℂ :=
  let _ := Fintype.ofFinite E
  ∑ x : E, if π x = 1 ∧ x * t * x⁻¹ = s then (1 : ℂ) else 0

/-- Induction of `f` along an injective homomorphism `ρ : E' →* E`, transporting `f` to `ρ.range`
and applying `Subgroup.indClassFun`. -/
noncomputable def induceClassFn (ρ : E' →* E) (hρ : Injective ρ) (f : E' → ℂ) : E → ℂ :=
  ρ.range.indClassFun (f ∘ (MulEquiv.ofInjective ρ hρ).symm)

/-- j is injective and r(γ) is a conjugation-equivariant (ord σ)-th root of j(γ) over σ, such
that any x ∈ ker π conjugating one r(δ) to an r(γ) lies in j(G). -/
@[local grind]
structure IsRootChoice (j : G →* E) (r : G → E) where
  /-- The homomorphism `j` is injective. -/
  injective : Injective j
  /-- `r γ` lies over `σ`. -/
  map_apply (γ : G) : π (r γ) = σ
  /-- The power of `r γ` by the order of `σ` is `j γ`. -/
  pow_orderOf (γ : G) : r γ ^ orderOf σ = j γ
  /-- The choice of roots is equivariant for conjugation by `G`. -/
  map_conj (v γ : G) : r (v * γ * v⁻¹) = j v * r γ * (j v)⁻¹
  /-- An element of the kernel of `π` that conjugates a chosen root to a chosen root lies in the
  image of `j`. -/
  mem_range_of_conj (x : E) (γ δ : G) : π x = 1 → x * r δ * x⁻¹ = r γ → x ∈ j.range

variable {π σ} {j : G →* E} {r : G → E} {ρ : E' →* E} {h : E' → ℂ} {g : E → ℂ} {α : Γ →* MulAut G}
  {Y : G → ℂ}

/-! ### Induction of class functions -/

/-- Conjugating `s` by `y` and `t` by `u`, where `u` and `y` have the same image under `π`, does not
change the number of elements of the kernel of `π` that conjugate `t` to `s`. -/
lemma conjCount_conj {u y : E} (h_eq : π u = π y) (s t : E) :
    conjCount π (y * s * y⁻¹) (u * t * u⁻¹) = conjCount π s t := by
  classical
  let _ := Fintype.ofFinite E
  -- The substitution `x ↦ y * x * u⁻¹` preserves the kernel of `π` and matches the conjugators.
  unfold conjCount
  refine (Fintype.sum_equiv ((Equiv.mulRight u⁻¹).trans (Equiv.mulLeft y)) _ _ fun x ↦ ?_).symm
  have h_ker : π (y * (x * u⁻¹)) = 1 ↔ π x = 1 := by simp [h_eq, ← mul_assoc]
  -- both sides are the same conjugation equation, moved by `y`
  have h_conj : y * (x * u⁻¹) * (u * t * u⁻¹) * (y * (x * u⁻¹))⁻¹ = y * s * y⁻¹ ↔
      x * t * x⁻¹ = s := by
    rw [show y * (x * u⁻¹) * (u * t * u⁻¹) * (y * (x * u⁻¹))⁻¹ = y * (x * t * x⁻¹) * y⁻¹ by group,
      mul_left_inj, mul_right_inj]
  simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight, h_ker, h_conj]

/-- If `h` is a `Z`-linear combination of characters of `E'`, then so is its induction
`induceClassFn ρ hρ h` along an injective homomorphism `ρ : E' →* E`. -/
lemma induceClassFn_mem_virtualChars {Z : Type*} [CommSemiring Z] [Algebra Z ℂ]
    (hρ : Injective ρ) (h_virtual : h ∈ virtualChars Z E') :
    induceClassFn ρ hρ h ∈ virtualChars Z E := by
  -- Induction of class functions is `Z`-linear and carries characters to characters.
  let L : (ρ.range → ℂ) →ₗ[Z] (E → ℂ) :=
    { toFun := ρ.range.indClassFun
      map_add' := ρ.range.indClassFun_add
      map_smul' c f := ρ.range.indClassFun_smul c f }
  exact Submodule.mapsTo_span (f := L) (s := {χ | IsChar χ})
    (fun _ ⟨V, hV⟩ ↦ ⟨TauCeti.indFDRep V, hV ▸ (ρ.range.indClassFun_ofFDRep_character V).symm⟩)
    (comp_mem_virtualChars h_virtual (MulEquiv.ofInjective ρ hρ).symm.toMonoidHom)

/-- When `π ∘ ρ` is surjective and `h` is a class function on `E'`, `induceClassFn ρ hρ h s` equals
the index of `ker(π ∘ ρ)` times the pairing of `conjCount π s ∘ ρ` with `h`. -/
private lemma induceClassFn_eq_index_mul_classInner [Finite Γ] (hρ : Injective ρ)
    (h_surj : Surjective (π.comp ρ)) (h_class : IsClassFunction h) (s : E) :
    induceClassFn ρ hρ h s = (π.comp ρ).ker.index * classInner (conjCount π s ∘ ρ) h := by
  classical
  let _ := Fintype.ofFinite E
  let _ := Fintype.ofFinite E'
  let _ := Fintype.ofFinite Γ
  let _ := Fintype.ofFinite π.ker
  let e : E' ≃* ρ.range := MulEquiv.ofInjective ρ hρ
  let f : ρ.range → ℂ := h ∘ e.symm
  have hf_conj (y u : ρ.range) : f (u * y * u⁻¹) = f y := by
    simpa [f, ← map_inv, ← map_mul] using h_class (e.symm y) (e.symm u)
  -- Every element of `E` factors uniquely as `x * ρ (u τ)` with `x ∈ ker π` and `τ ∈ Γ`.
  let u : Γ → E' := surjInv h_surj
  have hu (τ : Γ) : π (ρ (u τ)) = τ := surjInv_eq h_surj τ
  let decomp : π.ker × Γ ≃ E :=
    { toFun p := (p.1 : E) * ρ (u p.2)
      invFun y := (⟨y * (ρ (u (π y)))⁻¹, by simp [hu]⟩, π y)
      left_inv p := Prod.ext (Subtype.ext (by simp [hu])) (by simp [hu])
      right_inv y := by simp }
  -- Multiplying the representative on the right by `ρ (u τ) ∈ ρ.range` keeps its left coset.
  have h_sum_E : ∑ y : E, Function.indTerm f s y =
      Nat.card Γ * ∑ x : π.ker, Function.indTerm f s (x : E) := by
    rw [← Fintype.sum_equiv decomp _ _ fun _ ↦ rfl, Fintype.sum_prod_type, sum_comm]
    have h_term (τ : Γ) (x : π.ker) :
        Function.indTerm f s (decomp (x, τ)) = Function.indTerm f s (x : E) :=
      Function.indTerm_eq_of_mk_eq_of_conj f hf_conj s _ _
        (QuotientGroup.mk_mul_of_mem _ ⟨u τ, rfl⟩)
    simp [h_term, ← Nat.card_eq_fintype_card]
  have h_sum_ker : ∑ x : π.ker, Function.indTerm f s (x : E) =
      ∑ t : E', conj (conjCount π s (ρ t)) * h t := by
    have h_real (t : E') : conj (conjCount π s (ρ t)) = conjCount π s (ρ t) := by simp [conjCount]
    simp only [h_real, conjCount, sum_mul, ite_mul, one_mul, zero_mul]
    rw [sum_comm]
    simp only [ite_and, ← sum_filter]
    rw [← Finset.sum_subtype (univ.filter fun x : E ↦ π x = 1) (by simp [π.mem_ker])]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have h_eq_iff (t : E') : (x : E) * ρ t * (x : E)⁻¹ = s ↔ ρ t = (x : E)⁻¹ * s * (x : E) := by
      constructor <;> intro h_eq <;> [rw [← h_eq]; rw [h_eq]] <;> group
    simp only [Function.indTerm_apply, h_eq_iff]
    split_ifs with hx
    · have h_e : ρ (e.symm ⟨(x : E)⁻¹ * s * (x : E), hx⟩) = (x : E)⁻¹ * s * (x : E) :=
        congrArg Subtype.val (e.apply_symm_apply _)
      simp only [← h_e, hρ.eq_iff, sum_ite_eq', mem_univ, ↓reduceIte, f, comp_apply]
    · exact (Finset.sum_eq_zero fun t _ ↦ ite_eq_right fun ht ↦ hx ⟨t, ht⟩).symm
  have h_card_S : (Nat.card ρ.range : ℂ) = Nat.card E' := mod_cast (Nat.card_congr e.toEquiv).symm
  have h_ind_eq := ρ.range.indClassFun_eq_natCard_inv_mul_sum
    (IsUnit.mk0 (Nat.card ρ.range : ℂ) (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
    (TauCeti.ClassFunction.mem_iff.mpr hf_conj) s
  have h_idx : (π.comp ρ).ker.index = Nat.card Γ := by
    rw [index_ker, MonoidHom.range_eq_top.mpr h_surj, Nat.card_congr Subgroup.topEquiv.toEquiv]
  rw [induceClassFn, h_ind_eq, h_sum_E, h_sum_ker, h_card_S, h_idx, classInner, finMean_eq,
    Nat.card_eq_fintype_card]
  ring

/-! ### Semidirect products: existence of roots, extension of characters -/

/-- Let `S` be an algebra over the finite field `k'`, let `σ ∈ Gal(k'/k)` act on `Sˣ` through a
`σ`-semilinear ring endomorphism `τ`, and let `j` embed the finite group `G` onto the units fixed by
`σ`. Then there is `r : G → Sˣ ⋊ Gal(k'/k)` such that (a) `r` is a root choice: each `r γ` lies over
`σ`, is an `(ord σ)`-th root of `j γ` and is compatible with conjugation, and any unit conjugating
some `r δ` to some `r γ` lies in `j(G)`; and (b) the unit part of `r γ` lies in every
`k'`-subalgebra that contains `j γ`. -/
theorem exists_isRootChoice {k k' S : Type*} [Field k] [Field k'] [Algebra k k'] [Ring S]
    [Finite k'] [Algebra k' S] {β : Gal(k'/k) →* MulAut Sˣ} {σ : Gal(k'/k)} (τ : S →+* S)
    (hβ : ∀ u : Sˣ, β σ u = τ u) (hτ : Semiconj (algebraMap k' S) σ τ) {j : G →* Sˣ}
    (hj : Injective j) (h_range : ∀ u : Sˣ, u ∈ j.range ↔ β σ u = u) :
    ∃ r : G → Sˣ ⋊[β] Gal(k'/k),
      -- (a)
      IsRootChoice rightHom σ (inl.comp j) r ∧
      -- (b)
      ∀ (B : Subalgebra k' S) (γ : G), ↑(j γ) ∈ B → ↑(r γ).left ∈ B := by
  -- Let R = k'[C], with C cyclic of order |G| and σ acting on the coefficients. A generator of C
  -- is the norm of a unit z of R. Evaluate the generator at j γ and put r γ = (z(γ), σ).
  let C : Type := ZMod (Nat.card G)
  let s : k'[C] →+* k'[C] := (mapAlgAut k C σ).toRingHom
  -- the evaluation map R → S that sends the generator to j γ; it turns σ on R into τ on S
  let ev (γ : G) : k'[C] →ₐ[k'] S := lift k' S C
    ⟨⟨fun c : Multiplicative C ↦ j (γ ^ c.toAdd.val), by simp⟩, by simp [C, val_add, pow_add]⟩
  have h_fix (γ : G) : β σ (j γ) = j γ := (h_range (j γ)).mp ⟨γ, rfl⟩
  have h_ev (γ : G) (z : k'[C]) : τ (ev γ z) = ev γ (s z) := by
    induction z using induction_linear with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | single c x =>
      have hs_single : s (single c x) = single c (σ x) := by simp [s]
      rw [hs_single]
      simp only [ev, lift_single, MonoidHom.coe_mk, OneHom.coe_mk, Algebra.smul_def,
        map_mul, hτ.eq, ← hβ, h_fix]
  have h_tame : IsTameAtLevel s (orderOf σ) (algebraMap k' k'[C] 1) := by
    refine (isTameAtLevel_gal σ).of_semiconj (algebraMap k' k'[C]) (by simp [s, Semiconj]) ?_
    -- `mapAlgAut_apply` is left out: it turns `s` into `mapAlgEquiv k C σ`, whose power simp
    -- does not evaluate
    ext <;> simp [s, ← AlgEquiv.coe_pow, ← map_pow, -mapAlgAut_apply]
  -- `IsTameAtLevel.exists_prod_range_pow_apply_eq`: a σ-fixed unit of the finite ring R is the norm
  -- of a unit
  obtain ⟨z, -, -, hz_norm⟩ := h_tame.exists_prod_range_pow_apply_eq
    (.inl (Module.finite_of_finite k'))
    ((of k' C).toHomUnits (.ofAdd 1)).isUnit (by simp [s]) (one_dvd _)
  -- (u, σ)^m = (u σ(u) ⋯ σ^(m-1)(u), σ^m); for m the order of σ the product is the norm
  have h_pow_val (γ : G) (m : ℕ) :
      (((⟨z.map ↑(ev γ), σ⟩ : Sˣ ⋊[β] Gal(k'/k)) ^ m).left : S) =
        ev γ (∏ i ∈ range m, (s ^ i) z.val) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', SemidirectProduct.mul_left, Units.val_mul, hβ, ih, Units.coe_map,
        MonoidHom.coe_ofClass, h_ev, ← map_mul, map_prod, prod_range_succ']
      simp only [mul_comm (ev γ z.val), pow_succ']
      rfl
  have h_root (γ : G) : (⟨z.map ↑(ev γ), σ⟩ : Sˣ ⋊[β] Gal(k'/k)) ^ orderOf σ = inl (j γ) := by
    refine SemidirectProduct.ext (Units.ext ?_) (by rw [← map_pow rightHom]; exact pow_orderOf_eq_one σ)
    rw [h_pow_val, hz_norm, SemidirectProduct.left_inl]
    simp only [MonoidHom.coe_toHomUnits, of_apply, toAdd_ofAdd, ev, lift_single, one_smul,
      MonoidHom.coe_mk, OneHom.coe_mk, val_one_eq_one_mod, pow_mod_natCard, pow_one]
  -- z(γ) is a polynomial in j γ, so it follows conjugation
  have h_conj {γ : G} (δ : G) (u : Sˣ) (h_eq : j γ = u * j δ * u⁻¹) :
      z.map ↑(ev γ) = u * z.map ↑(ev δ) * u⁻¹ := by
    simp [Units.ext_iff, ev, lift_apply, Finsupp.sum, h_eq, u.conj_pow, mul_sum, sum_mul]
  refine ⟨fun γ ↦ ⟨z.map ↑(ev γ), σ⟩,
    { injective := inl_injective.comp hj
      map_apply := fun _ ↦ rfl
      pow_orderOf := h_root
      map_conj := fun v γ ↦ by ext <;> simp [(h_range _).1, h_conj γ (j v)]
      mem_range_of_conj := ?_ },
    fun B γ hγ ↦ by simp [ev, lift_apply, Finsupp.sum, sum_mem, B.smul_mem, pow_mem hγ]⟩
  -- if u conjugates r δ to r γ, it conjugates j δ to j γ (take powers) and so z(δ) to z(γ);
  -- comparing with u z(δ) σ(u)⁻¹ = z(γ) gives σ(u) = u
  rintro ⟨u, _⟩ γ δ rfl h_conj_root
  have h_j : j γ = u * j δ * u⁻¹ := by
    -- `mk_eq_inl_mul_inr` is left out: it splits `r γ` into `inl _ * inr σ`, and the power of
    -- that product is not reduced
    simpa [h_root, -mk_eq_inl_mul_inr] using
      congrArg (fun x ↦ (x ^ orderOf σ).left) h_conj_root.symm
  have h_fixed : β σ u = u := by
    simpa [h_conj δ u h_j] using congrArg SemidirectProduct.left h_conj_root
  obtain ⟨a, ha⟩ : ∃ a : G, j a = u := (h_range u).mpr h_fixed
  exact ⟨a, congrArg inl ha⟩

variable [Finite Γ] in
/-- A semidirect product of finite groups is finite. -/
instance : Finite (G ⋊[α] Γ) := .of_equiv _ equivProd.symm

open scoped Classical in
/-- On a semidirect product `G ⋊ Γ`, take the function equal to `u` on `G` and to `w` off `G`. Its
mean is the mean of `w` plus the difference of the means of `u` and `w` over `G`, divided by
`|Γ|`. -/
@[simp]
lemma finMean_ite [Finite Γ] (u w : G ⋊[α] Γ → ℂ) :
    finMean (fun x : G ⋊[α] Γ ↦ if x.right = 1 then u x else w x) =
      finMean w +
        (finMean (fun g : G ↦ u (inl g)) - finMean (fun g : G ↦ w (inl g))) / Nat.card Γ := by
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite Γ
  let _ := Fintype.ofFinite (G ⋊[α] Γ)
  have h_inl (g : G) : (equivProd.symm (g, 1) : G ⋊[α] Γ) = inl g := rfl
  -- The difference of the two sums is carried by the copy of G, and |G ⋊ Γ| = |G| |Γ|. The mean
  -- over `G ⋊ Γ` is moved to `G × Γ` (`↓`) before `finMean` is unfolded.
  simp [↓finMean_equiv equivProd.symm, finMean, ite_sub, ← sub_eq_iff_eq_add', ← sum_sub_distrib,
    field, finsum_eq_sum_of_fintype, Fintype.sum_prod_type, h_inl]

open scoped Classical in
/-- Let Y be a Γ-invariant irreducible character of G across a cyclic group Γ, and Φ a virtual
character of G⋊Γ with |Γ|⟨Φ,Φ⟩ = ⟨Φ|G,Φ|G⟩+|Γ|−1 and ⟨Y,Φ|G⟩ = 1+|Γ|m, m ∈ ℤ. Then the function
equal to Y on G and Φ off G is a character of G⋊Γ. -/
lemma IsIrreducibleChar.isChar_extend_semidirect [Finite Γ] [IsCyclic Γ] (hY : IsIrreducibleChar Y)
    (h_stable : ∀ (σ : Γ) (g : G), Y (α σ g) = Y g)
    {Φ : G ⋊[α] Γ → ℂ} (hΦ : Φ ∈ virtualChars ℤ (G ⋊[α] Γ))
    (h_self : Nat.card Γ * classInner Φ Φ = classInner (Φ ∘ inl) (Φ ∘ inl) + (Nat.card Γ - 1))
    (m : ℤ) (h_pair : classInner Y (Φ ∘ inl) = 1 + Nat.card Γ * m) :
    IsChar fun x : G ⋊[α] Γ ↦ if x.right = 1 then Y x.left else Φ x := by
  -- Extend `Y` across the cyclic quotient `Γ` (`TauCeti.exists_irreducibleCharacter_extension_iff`).
  -- By Gallagher's correspondence (`TauCeti.gallagher_bijOn`, via
  -- `TauCeti.irreducibleCharactersOver_eq_setOf_restrict_eq_of_isMulCommutative`), every
  -- irreducible character of `G ⋊ Γ` over `Y` restricts to `Y`, so its pairing with `f` is an
  -- integer and `eq_of_eq_sum_of_classInner_eq_intCast` identifies `f` with that constituent.
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite Γ
  let _ := Fintype.ofFinite (G ⋊[α] Γ)
  obtain ⟨⟨V, rfl⟩, hY_norm, -⟩ := hY
  set N : Subgroup (G ⋊[α] Γ) := rightHom.ker
  let _ := Fintype.ofFinite N
  let eN : G ≃* N :=
    (MulEquiv.ofInjective inl inl_injective).trans (MulEquiv.subgroupCongr range_inl_eq_ker_rightHom)
  let eQ : (G ⋊[α] Γ) ⧸ N ≃* Γ :=
    QuotientGroup.quotientKerEquivOfSurjective rightHom rightHom_surjective
  have : IsCyclic ((G ⋊[α] Γ) ⧸ N) := isCyclic_of_surjective eQ.symm.surjective
  let : CommGroup ((G ⋊[α] Γ) ⧸ N) := IsCyclic.commGroup
  let VN : FDRep ℂ N := .of (V.ρ.comp eN.symm.toMonoidHom)
  have heN_symm (n : N) : eN.symm n = n.1.left := by
    simpa [eN] using congrArg SemidirectProduct.left (congrArg Subtype.val (eN.apply_symm_apply n))
  have hVN_char (n : N) : VN.character n = V.character n.1.left := by
    simp [VN, FDRep.character_of, Representation.character_comp, heN_symm]
  have hθ : VN.character ∈ TauCeti.irreducibleCharacters ℂ N := by
    refine TauCeti.mem_irreducibleCharacters_of_characterPairing_self_eq_one
      (f := TauCeti.ClassFunction.ofFDRep VN) (TauCeti.character_mem_virtualCharacters VN) ?_
      (n := Module.finrank ℂ V) (by simp [VN, FDRep.char_one])
    rw [TauCeti.ClassFunction.characterPairing_ofFDRep,
      ← Fintype.sum_equiv eN _ _ fun g ↦ by simp [hVN_char, ← map_inv, ← V.conj_char],
      Nat.card_congr eN.symm.toEquiv]
    simpa [classInner, finMean_eq, Nat.card_eq_fintype_card, div_eq_inv_mul, mul_comm] using hY_norm
  obtain ⟨σ₀, hσ₀⟩ := isCyclic_iff_exists_zpowers_eq_top.mp ‹IsCyclic Γ›
  have h_gen : Subgroup.zpowers (QuotientGroup.mk' N (inr σ₀)) = ⊤ :=
    eq_top_iff.mpr fun q _ ↦ by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hσ₀.ge (Subgroup.mem_top (eQ q)))
      exact ⟨k, eQ.injective (by simpa [eQ] using hk)⟩
  have h_conj_stable : VN.character ∘ MulAut.conjNormal (inr σ₀) = VN.character := by
    funext n
    have hn_right : n.1.right = 1 := rightHom.mem_ker.mp n.2
    have h_left : ((MulAut.conjNormal (inr σ₀) n : N) : G ⋊[α] Γ).left = α σ₀ n.1.left := by
      simp [MulAut.conjNormal_apply, SemidirectProduct.mul_left, hn_right]
    rw [comp_apply, hVN_char, hVN_char, h_left, h_stable]
  obtain ⟨χ₀, hχ₀, hχ₀_res⟩ :=
    (TauCeti.exists_irreducibleCharacter_extension_iff h_gen hθ).mpr h_conj_stable
  have h_over := TauCeti.irreducibleCharactersOver_eq_setOf_restrict_eq_of_isMulCommutative
    hχ₀ hθ (congrFun hχ₀_res)
  -- Expand in the irreducible characters of `G ⋊ Γ` and apply `eq_of_eq_sum_of_classInner_eq_intCast`.
  set f : G ⋊[α] Γ → ℂ := fun x ↦ if x.right = 1 then V.character x.left else Φ x
  set I : G ⋊[α] Γ → ℂ := fun x ↦ if x.right = 1 then V.character x.left else 0
  have hf_class : IsClassFunction f := by
    simp +contextual [f, V.char_conj, isClassFunction_of_mem_virtualChars hΦ, h_stable]
  have hI_class : IsClassFunction I := by simp +contextual [I, V.char_conj, h_stable]
  let _ : Invertible (Nat.card (G ⋊[α] Γ) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let χ := TauCeti.irreducibleCharacter ℂ (G := G ⋊[α] Γ)
  have hχ_char (j) : IsChar (χ j) := by
    obtain ⟨W, hW⟩ := TauCeti.irreducibleCharacters_subset_range (TauCeti.irreducibleCharacter_mem ℂ j)
    exact ⟨W, hW⟩
  have h_exp {φ : G ⋊[α] Γ → ℂ} (hφ : IsClassFunction φ) :
      φ = ∑ j, classInner (χ j) φ • χ j := by
    funext x
    have hx := TauCeti.ClassFunction.apply_eq_sum_characterPairing_mul_character
      (TauCeti.irreducibleRepresentation ℂ) (TauCeti.pairwise_isEmpty_equiv_irreducibleRepresentation ℂ)
      (by simp) ⟨φ, TauCeti.ClassFunction.mem_iff.mpr hφ⟩ x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine hx.trans (Finset.sum_congr rfl fun j _ ↦ congrArg (· * _) ?_)
    rw [TauCeti.ClassFunction.characterPairing_apply, classInner, finMean_eq,
      Nat.card_eq_fintype_card, div_eq_inv_mul]
    congr 1
    exact Finset.sum_congr rfl fun y _ ↦ by
      simp [χ, ← (hχ_char j).apply_inv, TauCeti.character_irreducibleRepresentation]
  have h_If : classInner I f ≠ 0 := by
    have h_fun : (fun x ↦ conj (I x) * f x) =
        fun x : G ⋊[α] Γ ↦ if x.right = 1 then conj (V.character x.left) * V.character x.left else 0 := by
      ext x; split_ifs <;> simp [I, f]
    rw [classInner, h_fun, finMean_ite]
    simp [← classInner.eq_1, hY_norm, finMean_eq, Fintype.card_pos.ne']
  rw [classInner_eq_sum_of_eq_sum (h_exp hI_class)] at h_If
  obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero h_If
  obtain ⟨hI_ne, hf_ne⟩ : classInner (χ i) I ≠ 0 ∧ classInner (χ i) f ≠ 0 := by simpa using hi
  have h_res_i (g : G) : χ i (inl g) = V.character g := by
    have h_pair_G : classInner (χ i ∘ inl) V.character ≠ 0 := by
      intro h0
      have h_split : classInner (χ i) I = classInner (χ i ∘ inl) V.character / Nat.card Γ := by
        simp +contextual [classInner, I]
      exact hI_ne (by simp [h_split, h0])
    have h_mem_over : χ i ∈ TauCeti.irreducibleCharactersOver ℂ N VN.character := by
      rw [TauCeti.mem_irreducibleCharactersOver_iff_sum]
      refine ⟨TauCeti.irreducibleCharacter_mem ℂ i, ?_⟩
      rw [← Fintype.sum_equiv eN _ _ fun g ↦ by simp [hVN_char, ← map_inv, ← V.conj_char]]
      intro h_sum
      apply h_pair_G
      rw [classInner, finMean_eq, ← Fintype.sum_equiv (.inv G) _ _ fun g ↦ by
        simp [← (hχ_char i).apply_inv, ← V.conj_char, mul_comm]]
      simp [h_sum]
    rw [h_over] at h_mem_over
    simpa [hVN_char] using h_mem_over.2 ⟨inl g, rightHom_inl g⟩
  obtain ⟨M, hM⟩ : ∃ M : ℤ, classInner (χ i) Φ = algebraMap ℤ ℂ M :=
    (hχ_char i).exists_classInner_eq hΦ
  have hm_eq : classInner (χ i) f = (M - m : ℤ) := by
    have h_split : classInner (χ i) f =
        classInner (χ i) Φ +
          (classInner (χ i ∘ inl) V.character - classInner (χ i ∘ inl) (Φ ∘ inl)) / Nat.card Γ := by
      simp +contextual [classInner, f]
    have h_comp_eq : χ i ∘ inl = V.character := funext h_res_i
    rw [h_split, hM, h_comp_eq, hY_norm, h_pair, eq_intCast]
    have : (Nat.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    field_simp
    push_cast
    ring
  have hf_norm : classInner f f = 1 := by
    have h_split : classInner f f =
        classInner Φ Φ + (classInner V.character V.character - classInner (Φ ∘ inl) (Φ ∘ inl)) / Nat.card Γ := by
      simp +contextual [classInner, f]
    have : (Nat.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    rw [h_split, hY_norm]
    field_simp
    linear_combination h_self
  have hf_eq := eq_of_eq_sum_of_classInner_eq_intCast (h_exp hf_class) hf_norm
    (by simp [f, FDRep.char_one])
    (by simpa [χ, TauCeti.irreducibleCharacter_one] using TauCeti.characterDegree_pos ℂ i)
    hm_eq (by simpa [hm_eq] using hf_ne)
  exact hf_eq ▸ hχ_char i

omit [Finite E] [Finite G] in
lemma IsRootChoice.apply_emb_eq_one (R : IsRootChoice π σ j r) (γ : G) : π (j γ) = 1 := by
  rw [← R.pow_orderOf γ, map_pow, R.map_apply, pow_orderOf_eq_one]

/-- For a choice of roots `r`, the image of `j` in the kernel of `π`. -/
private abbrev IsRootChoice.rangeInKer (R : IsRootChoice π σ j r) : Subgroup π.ker :=
  (j.codRestrict π.ker R.apply_emb_eq_one).range

/-- For a choice of roots `r`, the map `(x, γ) ↦ x r(γ) x⁻¹` from `(ker π ⧸ j(G)) × G` to the coset
of `σ`, with `x` the chosen representative of its class. -/
private noncomputable def IsRootChoice.conjRoot (R : IsRootChoice π σ j r)
    (z : (π.ker ⧸ R.rangeInKer) × G) : π ⁻¹' {σ} :=
  ⟨(z.fst.out : E) * r z.snd * (z.fst.out : E)⁻¹, by
    simp [π.mem_ker.mp z.fst.out.property, R.map_apply]⟩

omit [Finite E] [Finite G] in
/-- For a choice of roots, the coset of `σ` has as many elements as the kernel of `π`. -/
private lemma IsRootChoice.card_preimage_eq (R : IsRootChoice π σ j r) :
    Nat.card (π ⁻¹' {σ}) = Nat.card π.ker := by
  rw [← R.map_apply 1]
  exact Nat.card_congr (π.fiberEquivKer _)

/-- For a choice of roots, `IsRootChoice.conjRoot` is a bijection onto the coset of `σ`: it is
injective by `IsRootChoice.mem_range_of_conj`, and both sides have `|ker π|` elements. -/
private lemma IsRootChoice.bijective_conjRoot (R : IsRootChoice π σ j r) :
    Bijective R.conjRoot := by
  have h_ker (x : π.ker) : π x = 1 := π.mem_ker.mp x.property
  have h_inj : Injective R.conjRoot := by
    rintro ⟨y, δ⟩ ⟨x, γ⟩ hc
    have h_val : (R.conjRoot (x, γ) : E) = R.conjRoot (y, δ) := congrArg Subtype.val hc.symm
    have h_conj : (y.out⁻¹ * x.out : π.ker) * r γ * ((y.out⁻¹ * x.out : π.ker) : E)⁻¹ = r δ := by
      simpa [IsRootChoice.conjRoot, mul_assoc] using
        congrArg (fun t : E ↦ (y.out : E)⁻¹ * t * y.out) h_val
    obtain ⟨a, ha⟩ : ∃ a : G, j a = (y.out⁻¹ * x.out : π.ker) :=
      R.mem_range_of_conj (y.out⁻¹ * x.out : π.ker) δ γ (h_ker _) h_conj
    have h_coset : y.out⁻¹ * x.out ∈ R.rangeInKer := ⟨a, Subtype.ext ha⟩
    obtain rfl : y = x := y.out_equiv_out.mp (QuotientGroup.leftRel_apply.mpr h_coset)
    -- equal roots have equal powers `j δ = j γ`, and `j` is injective
    have h_root : r δ = r γ := by simpa [IsRootChoice.conjRoot] using hc
    have h_j_eq : j δ = j γ := by rw [← R.pow_orderOf δ, ← R.pow_orderOf γ, h_root]
    rw [R.injective h_j_eq]
  have h_card_le : Nat.card (π ⁻¹' {σ}) ≤ Nat.card ((π.ker ⧸ R.rangeInKer) × G) := by
    rw [R.card_preimage_eq, ← R.rangeInKer.index_mul_card, Nat.card_prod]
    exact mul_le_mul_right (Finite.card_range_le _) _
  exact h_inj.bijective_of_nat_card_le h_card_le

/-- For a choice of roots `r`, every element `s` of `E` over `σ` is conjugate to some `r γ` by an
element of the kernel of `π`. -/
lemma IsRootChoice.exists_conj_eq_of_map_eq (R : IsRootChoice π σ j r) {s : E}
    (hs : π s = σ) : ∃ (x : E) (γ : G), π x = 1 ∧ x * r γ * x⁻¹ = s := by
  obtain ⟨⟨x, γ⟩, hc⟩ := R.bijective_conjRoot.surjective ⟨s, hs⟩
  exact ⟨x.out, γ, π.mem_ker.mp x.out.property, congrArg Subtype.val hc⟩

open scoped Classical in
/-- For a choice of roots `r`, let `h` and `g` descend on the coset of `σ` to `f` and `f'` and be
invariant under conjugation by the kernel of `π`. Then the index of the kernel times the mean of
`conj h * g` over `E`, taken as zero off the coset of `σ`, is the inner product of `f` and `f'`. -/
lemma IsRootChoice.index_mul_finMean_eq_classInner [Finite Γ]
    (R : IsRootChoice π σ j r) {h g : E → ℂ}
    {f f' : G → ℂ} (hh : DescendsOnCoset π σ j h f) (hg : DescendsOnCoset π σ j g f')
    (hh_conj : ∀ s x : E, π x = 1 → h (x * s * x⁻¹) = h s)
    (hg_conj : ∀ s x : E, π x = 1 → g (x * s * x⁻¹) = g s) :
    π.ker.index * finMean (fun s : E ↦ if π s = σ then conj (h s) * g s else 0) =
      classInner f f' := by
  -- Reindex the sum over the coset by `IsRootChoice.conjRoot`; the terms do not depend on `x`.
  let _ := Fintype.ofFinite E
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite (π.ker ⧸ R.rangeInKer)
  let _ := Fintype.ofFinite (π ⁻¹' {σ})
  have h_ker (x : π.ker) : π x = 1 := π.mem_ker.mp x.property
  have h_sum :
      (∑ s : E, if π s = σ then conj (h s) * g s else 0) =
        (Nat.card (π.ker ⧸ R.rangeInKer) : ℂ) * ∑ γ : G, conj (f γ) * f' γ := by
    rw [← sum_filter, ← Finset.sum_subtype (univ.filter fun s : E ↦ π s = σ) (by simp),
      ← Fintype.sum_equiv (Equiv.ofBijective _ R.bijective_conjRoot) _ _ fun _ ↦ rfl,
      Fintype.sum_prod_type]
    have h_term (x : π.ker ⧸ R.rangeInKer) (γ : G) :
        conj (h (R.conjRoot (x, γ))) * g (R.conjRoot (x, γ)) = conj (f γ) * f' γ := by
      have hx := h_ker x.out
      rw [IsRootChoice.conjRoot, hh_conj _ _ hx, hg_conj _ _ hx,
        hh (r γ) γ (R.map_apply γ) (R.pow_orderOf γ),
        hg (r γ) γ (R.map_apply γ) (R.pow_orderOf γ)]
    simp only [h_term, sum_const, card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [classInner, finMean, finMean_eq, finsum_eq_sum_of_fintype, h_sum, ← π.ker.index_mul_card,
    ← R.card_preimage_eq, ← Nat.card_eq_of_bijective _ R.bijective_conjRoot, Nat.card_prod,
    ← Nat.card_eq_fintype_card]
  have h_index : (π.ker.index : ℂ) ≠ 0 := mod_cast index_ne_zero_of_finite
  have h_quot : (Nat.card (π.ker ⧸ R.rangeInKer) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h_G : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  push_cast
  field_simp

omit [Finite E] [Finite G] in
/-- A choice of roots restricts to a subgroup `H` of `E` and its preimage `H₀` in `G`, if the
roots of the elements of `H₀` lie in `H`. -/
lemma IsRootChoice.restrict_subgroup (R : IsRootChoice π σ j r) (H : Subgroup E) {H₀ : Subgroup G}
    (h_comap : comap j H = H₀) (h_mem : ∀ γ ∈ H₀, r γ ∈ H) :
    IsRootChoice (G := H₀) (π.comp H.subtype) σ (j.restrict h_comap.ge)
      fun γ : H₀ ↦ ⟨r γ, h_mem γ γ.property⟩ := by
  refine ⟨?_, fun γ ↦ R.map_apply γ, fun γ ↦ Subtype.ext (R.pow_orderOf γ),
    fun v γ ↦ Subtype.ext (R.map_conj v γ), fun u γ δ hu h_conj ↦ ?_⟩
  · exact fun a b h_eq ↦ Subtype.ext (R.injective (congrArg Subtype.val h_eq))
  -- An element `u` of `H ⊓ π.ker` that conjugates two roots is `j a`, and `a ∈ H₀` as `j a ∈ H`.
  obtain ⟨a, ha⟩ : ∃ a : G, j a = u := R.mem_range_of_conj u γ δ hu (congrArg Subtype.val h_conj)
  exact ⟨⟨a, h_comap.le (by simp [mem_comap, ha])⟩, Subtype.ext ha⟩

/-- Given a choice of roots `r`, a function `g` on `E` that is invariant under conjugation by the
kernel of `π` descends on the coset over `σ` to `g ∘ r`. -/
lemma IsRootChoice.descendsOnCoset_comp (R : IsRootChoice π σ j r)
    (h_inv : ∀ s x : E, π x = 1 → g (x * s * x⁻¹) = g s) :
    DescendsOnCoset π σ j g (g ∘ r) := by
  intro s γ hs h_pow
  -- Restrict the roots to the centraliser of `j γ`, which holds `s` as `s ^ orderOf σ = j γ`.
  have h_root : ∀ δ ∈ (centralizer {j γ}).comap j, r δ ∈ centralizer {j γ} := by
    simp_all [← map_mul, R.injective.eq_iff, ← R.map_conj, ← mul_inv_eq_iff_eq_mul,
      mem_centralizer_iff]
  have h_mem : s ∈ centralizer {j γ} := by simp [← h_pow, pow_mul_comm', mem_centralizer_iff]
  -- There `s` is conjugate to a root `r δ` by some `x` in the kernel of `π`. The power `orderOf σ`
  -- gives `x * j δ * x⁻¹ = j γ`, and `x` commutes with `j γ`, so `δ = γ`.
  obtain ⟨⟨x, hx⟩, δ, h_ker, h_s⟩ :=
    (R.restrict_subgroup (centralizer {j γ}) rfl h_root).exists_conj_eq_of_map_eq
      (s := ⟨s, h_mem⟩) hs
  have h_s_eq : x * r δ * x⁻¹ = s := congrArg Subtype.val h_s
  have h_conj_pow : x * j δ * x⁻¹ = j γ := by
    calc x * j δ * x⁻¹ = (x * r δ * x⁻¹) ^ orderOf σ := by rw [conj_pow, R.pow_orderOf δ]
      _ = j γ := by rw [h_s_eq, h_pow]
  have h_comm : j γ * x = x * j γ := mem_centralizer_iff.mp hx (j γ) rfl
  have h_j_eq : j δ = j γ := mul_left_cancel <| by rwa [← h_comm, ← mul_inv_eq_iff_eq_mul]
  change g s = g (r γ)
  rw [← h_s_eq, h_inv (r δ) x h_ker, R.injective h_j_eq]

omit [Finite G] in
/-- For a choice of roots `r`, the number of elements of the kernel of `π` that conjugate `r δ` to
`r γ` is the number of `v : G` with `δ = v⁻¹ * γ * v`. -/
private lemma IsRootChoice.conjCount_root (R : IsRootChoice π σ j r) [Fintype G] [DecidableEq G]
    (γ δ : G) :
    conjCount π (r γ) (r δ) = ∑ v : G, if δ = (MulAut.conj v)⁻¹ • γ then 1 else 0 := by
  classical
  let _ := Fintype.ofFinite E
  have h_r_inj : Injective r :=
    fun a b h_eq ↦ R.injective (by rw [← R.pow_orderOf a, ← R.pow_orderOf b, h_eq])
  -- only the elements of `j G` contribute, by `IsRootChoice.mem_range_of_conj`
  refine (Fintype.sum_of_injective j R.injective _ _ ?_ ?_).symm
  · intro x hx
    exact ite_eq_right fun ⟨hx_ker, hx_conj⟩ ↦ hx (R.mem_range_of_conj x γ δ hx_ker hx_conj)
  · -- `↓`: `eq_inv_smul_iff` must act before the action is unfolded to `v⁻¹ * γ * v`
    simp [R.apply_emb_eq_one, ← R.map_conj, ↓eq_inv_smul_iff, h_r_inj.eq_iff]

/-- Descent commutes with induction. Let `ρ₀ : G' → G` be compatible with injective `ρ : E' →* E`,
with choices of roots on both sides and `π ∘ ρ` surjective. If the class function `h` descends to
`f`, and the class function `F` is induced from `f` along `ρ₀` in the sense of Frobenius
reciprocity (`hF`), then `induceClassFn ρ hρ h` descends to `F`. -/
lemma DescendsOnCoset.induce [Finite Γ]
    (R : IsRootChoice π σ j r) (hρ : Injective ρ) (h_surj : Surjective (π.comp ρ))
    (h_class : IsClassFunction h) (ρ₀ : G' → G)
    {j' : G' →* E'} (h_comm : ∀ γ : G', ρ (j' γ) = j (ρ₀ γ)) {f : G' → ℂ} {r' : G' → E'}
    (R' : IsRootChoice (π.comp ρ) σ j' r') (h_lift : DescendsOnCoset (π.comp ρ) σ j' h f)
    {F : G → ℂ} (hF_class : IsClassFunction F)
    (hF : ∀ χ : G → ℂ, IsClassFunction χ → classInner F χ = classInner f (χ ∘ ρ₀)) :
    DescendsOnCoset π σ j (induceClassFn ρ hρ h) F := by
  classical
  let _ := Fintype.ofFinite E
  let _ := Fintype.ofFinite G
  -- By `IsRootChoice.index_mul_finMean_eq_classInner` for the roots r', the value of the induced
  -- function at s is the pairing on G' of the count `δ ↦ conjCount π s (r δ)`, pulled back by ρ₀,
  -- with f. By `hF` this is the conjugate of the pairing of F with that count on G, which is F γ.
  intro s γ hs hγ
  have h_conj_snd (t x : E) (hx : π x = 1) :
      conjCount π s (x * t * x⁻¹) = conjCount π s t := by
    simpa using conjCount_conj (hx.trans π.map_one.symm) s t
  have h_conj_fst (t t' x : E) (hx : π x = 1) :
      conjCount π (x * t' * x⁻¹) t = conjCount π t' t := by
    simpa using conjCount_conj (hx.trans π.map_one.symm).symm t' t
  -- the count vanishes off the coset of σ
  have h_coset : (fun t ↦ conj (conjCount π s (ρ t)) * h t) =
      fun t ↦ if π.comp ρ t = σ then conj (conjCount π s (ρ t)) * h t else 0 := by
    ext t
    split_ifs with ht
    · rfl
    · have h0 : conjCount π s (ρ t) = 0 := by
        refine Finset.sum_eq_zero fun x _ ↦ ite_eq_right ?_
        rintro ⟨hx, h_eq⟩
        apply ht
        have hπ := congrArg π h_eq
        simp only [map_mul, map_inv, hx, one_mul, inv_one, mul_one, hs] at hπ
        exact hπ
      rw [h0, map_zero, zero_mul]
  have h_lifts :
      DescendsOnCoset (π.comp ρ) σ j' (conjCount π s ∘ ρ) ((conjCount π s ∘ r) ∘ ρ₀) := by
    intro t δ ht hδ
    have h_pow_eq : ρ t ^ orderOf σ = j (ρ₀ δ) := by rw [← map_pow, hδ, h_comm]
    exact R.descendsOnCoset_comp h_conj_snd (ρ t) (ρ₀ δ) ht h_pow_eq
  have h_induce : induceClassFn ρ hρ h s = classInner ((conjCount π s ∘ r) ∘ ρ₀) f := by
    rw [induceClassFn_eq_index_mul_classInner hρ h_surj h_class]
    change ((π.comp ρ).ker.index : ℂ) * finMean (fun t ↦ conj (conjCount π s (ρ t)) * h t) = _
    rw [h_coset]
    exact R'.index_mul_finMean_eq_classInner h_lifts h_lift
      (fun t x hx ↦ by simpa using h_conj_snd (ρ t) (ρ x) hx) fun t x _ ↦ h_class t x
  have h_count (δ : G) :
      conjCount π s (r δ) = ∑ v : G, if δ = (MulAut.conj v)⁻¹ • γ then 1 else 0 := by
    -- `s` may be replaced by the root `r γ`
    have h_at_root : conjCount π s (r δ) = conjCount π (r γ) (r δ) :=
      R.descendsOnCoset_comp (g := fun t ↦ conjCount π t (r δ)) (h_conj_fst _) s γ hs hγ
    rw [h_at_root, R.conjCount_root γ δ]
  have h_count_class : IsClassFunction (conjCount π s ∘ r) := fun γ v ↦ by
    change conjCount π s (r (v * γ * v⁻¹)) = conjCount π s (r γ)
    rw [R.map_conj, h_conj_snd _ _ (R.apply_emb_eq_one v)]
  -- the count is real, so swapping the two sides of a pairing with it conjugates the pairing
  have h_count_real (t : E) : conj (conjCount π s t) = conjCount π s t := by
    simp [conjCount]
  -- `F` is a class function, so the mean over `δ` of the count at `r δ` times `F δ` is `F γ`
  have h_mean_count : classInner (conjCount π s ∘ r) F = F γ := by
    -- each `v` contributes `F (v⁻¹ * γ * v) = F γ`
    have h_sum : ∑ δ : G, conj (conjCount π s (r δ)) * F δ = Nat.card G * F γ := by
      -- `sum_boole` is left out so that the count stays a sum over `v` and the sums can be swapped;
      -- `inv_inv` is left out so that `hF_class` matches `v⁻¹ * γ * v⁻¹⁻¹`
      simp [h_count, apply_ite conj, -sum_boole, sum_comm (γ := G), ← map_inv,
        hF_class, -inv_inv, sum_mul]
    simp [classInner, finMean_eq, h_sum, ← Nat.card_eq_fintype_card, Nat.card_pos.ne']
  calc induceClassFn ρ hρ h s
      = classInner ((conjCount π s ∘ r) ∘ ρ₀) f := h_induce
    _ = conj (classInner f ((conjCount π s ∘ r) ∘ ρ₀)) := by
        simp [classInner, ← finMean_conj, h_count_real, mul_comm]
    _ = conj (classInner F (conjCount π s ∘ r)) := by rw [hF _ h_count_class]
    _ = classInner (conjCount π s ∘ r) F := by
        simp [classInner, ← finMean_conj, h_count_real, mul_comm]
    _ = F γ := h_mean_count

end CosetRoots

end New
