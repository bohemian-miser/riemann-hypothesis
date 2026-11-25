module

import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.SplittingOfPositiveLevel
import Mathlib.Tactic.Linter.Style
public import Formalism.DistinguishedUnitIdeals.StatementE

@[expose] public section

noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

namespace IdempotentNormalFormsRhoFacts

open S1

section basic
variable {O : Type} [CommRing O] {V : Type} [AddCommGroup V] [Module (PowerSeries O) V]

theorem smul_mem_sm (a : PowerSeries O) {S : Submodule (PowerSeries O) V} {u : V} (hu : u ∈ S) :
    a • u ∈ sm a S :=
  mem_sm.2 ⟨u, hu, rfl⟩

theorem sm_of_span {a b : PowerSeries O} (h : b ∈ Ideal.span {a})
    {S : Submodule (PowerSeries O) V} {u : V} (hu : u ∈ S) : b • u ∈ sm a S := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
  exact mem_sm.2 ⟨c • u, S.smul_mem c hu, by rw [smul_smul, mul_comm]⟩

theorem alg_C (f : PowerSeries O →ₐ[O] PowerSeries O) (m : O) : f (C m) = C m := by
  simpa [PowerSeries.algebraMap_apply] using f.commutes m

theorem it_C (f : PowerSeries O →ₐ[O] PowerSeries O) (k : ℕ) (m : O) : (⇑f)^[k] (C m) = C m :=
  Function.iterate_fixed (alg_C f m) k

theorem lc_pow (B : Base O) (K : ℕ) : B.lc ^ K = C ((B.ℓ : O) ^ K) := by
  simp only [Base.lc, map_pow]

end basic

section lat
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] (L : Lat B n V)

theorem phiIt_C (i : ZMod n) (k : ℕ) (m : O) (v : V) :
    L.phiIt i k (C m • v) = C m • L.phiIt i k v := by
  rw [phiIt_smul, it_C]

theorem γ_C (i : ZMod n) (m : O) (v : V) : L.γ i (C m • v) = C m • L.γ i v := by
  rw [L.γ_semi, alg_C]

theorem φ_C (i : ZMod n) (m : O) (v : V) : L.φ i (C m • v) = C m • L.φ i v := by
  rw [L.φ_semi, alg_C]

theorem γ_sm {a : PowerSeries O} (ha : B.γ a ∈ Ideal.span {a}) {i : ZMod n}
    {S : Submodule (PowerSeries O) V} (hS : ∀ v ∈ S, L.γ i v ∈ S) {v : V} (hv : v ∈ sm a S) :
    L.γ i v ∈ sm a S := by
  obtain ⟨u, hu, rfl⟩ := mem_sm.1 hv
  rw [L.γ_semi]
  exact sm_of_span ha (hS u hu)

theorem γ_pow_span {a : PowerSeries O} (ha : B.γ a ∈ Ideal.span {a}) (M : ℕ) :
    B.γ (a ^ M) ∈ Ideal.span {a ^ M} := by
  rw [map_pow]
  exact Ideal.mem_span_singleton.2 (pow_dvd_pow_of_dvd (Ideal.mem_span_singleton.1 ha) M)

theorem dγ_single (k : ZMod n) (r : V) :
    L.dγ (Pi.single k r) = Pi.single k (L.γ k r - r) := by
  funext i
  simp only [Lat.dγ]
  by_cases h : i = k
  · subst h
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h, map_zero, sub_zero]

theorem dφ_dγ (m : ZMod n → V) : L.dφ (L.dγ m) = L.dγ (L.dφ m) := by
  funext i
  simp only [Lat.dφ, Lat.dγ, map_sub, L.comm]
  abel

theorem dγ_sub (a b : ZMod n → V) : L.dγ (a - b) = L.dγ a - L.dγ b := by
  funext i
  simp only [Lat.dγ, map_sub, Pi.sub_apply]
  abel

theorem dφ_sub (a b : ZMod n → V) : L.dφ (a - b) = L.dφ a - L.dφ b := by
  funext i
  simp only [Lat.dφ, map_sub, Pi.sub_apply]
  abel

theorem dγ_C (m : O) (a : ZMod n → V) : L.dγ (C m • a) = C m • L.dγ a := by
  funext i
  simp only [Lat.dγ, Pi.smul_apply, γ_C, smul_sub]

theorem dφ_C (m : O) (a : ZMod n → V) : L.dφ (C m • a) = C m • L.dφ a := by
  funext i
  simp only [Lat.dφ, Pi.smul_apply, φ_C, smul_sub]

variable {L}

theorem isTr_sub {c : ZMod n} {j M g sig : ℕ} {z₁ z₂ τ₁ τ₂ : V}
    (h₁ : L.IsTr c j M g sig z₁ τ₁) (h₂ : L.IsTr c j M g sig z₂ τ₂) :
    L.IsTr c j M g sig (z₁ - z₂) (τ₁ - τ₂) := by
  obtain ⟨hp₁, K₁, v₁, hv₁, hg₁, ht₁⟩ := h₁
  obtain ⟨hp₂, K₂, v₂, hv₂, hg₂, ht₂⟩ := h₂
  refine ⟨Submodule.sub_mem _ hp₁ hp₂, K₁ + K₂, B.lc ^ K₂ • v₁ - B.lc ^ K₁ • v₂,
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hv₁) (Submodule.smul_mem _ _ hv₂), ?_, ?_⟩
  · have e : L.γ c (B.lc ^ K₂ • v₁ - B.lc ^ K₁ • v₂) - (B.lc ^ K₂ • v₁ - B.lc ^ K₁ • v₂)
        - B.lc ^ (K₁ + K₂) • (z₁ - z₂)
        = B.lc ^ K₂ • (L.γ c v₁ - v₁ - B.lc ^ K₁ • z₁)
          - B.lc ^ K₁ • (L.γ c v₂ - v₂ - B.lc ^ K₂ • z₂) := by
      rw [map_sub, gam_lc_smul, gam_lc_smul, pow_add]
      simp only [smul_sub, smul_smul, mul_comm]
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hg₁) (Submodule.smul_mem _ _ hg₂)
  · have e : B.lc ^ (K₁ + K₂) • (τ₁ - τ₂)
        - B.lc ^ sig • L.phiIt c j (B.lc ^ K₂ • v₁ - B.lc ^ K₁ • v₂)
        = B.lc ^ K₂ • (B.lc ^ K₁ • τ₁ - B.lc ^ sig • L.phiIt c j v₁)
          - B.lc ^ K₁ • (B.lc ^ K₂ • τ₂ - B.lc ^ sig • L.phiIt c j v₂) := by
      rw [phiIt_sub, phiIt_lc, phiIt_lc, pow_add]
      simp only [smul_sub, smul_smul, mul_comm]
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ht₁) (Submodule.smul_mem _ _ ht₂)

theorem isTr_C {c : ZMod n} {j M g sig : ℕ} {z τ : V} (m : O)
    (h : L.IsTr c j M g sig z τ) : L.IsTr c j M g sig (C m • z) (C m • τ) := by
  obtain ⟨hτ, K, v, hv, hz, hf⟩ := h
  refine ⟨Submodule.smul_mem _ _ hτ, K, C m • v, Submodule.smul_mem _ _ hv, ?_, ?_⟩
  · have e : (L.γ c (C m • v) - C m • v) - B.lc ^ K • (C m • z) =
        C m • ((L.γ c v - v) - B.lc ^ K • z) := by
      rw [γ_C]
      simp only [smul_sub, smul_smul, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ _ hz
  · have e : B.lc ^ K • (C m • τ) - B.lc ^ sig • L.phiIt c j (C m • v) =
        C m • (B.lc ^ K • τ - B.lc ^ sig • L.phiIt c j v) := by
      rw [phiIt_C]
      simp only [smul_sub, smul_smul, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ _ hf

theorem isTr_self {c : ZMod n} (j M g sig : ℕ) {u : V} (hu : u ∈ sm X (L.N c)) :
    L.IsTr c j M g sig (L.γ c u - u) (B.lc ^ sig • L.phiIt c j u) := by
  refine ⟨Submodule.smul_mem _ _ (mem_pull _ c j (sm_le X _ hu)), 0, u, hu, ?_, ?_⟩ <;>
    simp only [pow_zero, one_smul, sub_self, zero_mem]

theorem isTr_zero {c : ZMod n} {j M g sig : ℕ} {τ : V}
    (h3 : ((⇑B.φ)^[j] X) ^ M ∈ Ideal.span {B.ff j M g})
    (h6 : ∀ v ∈ sm X (L.N c), L.γ c v - v ∈ sm (X ^ M) (L.N c) →
      ∃ K : ℕ, B.lc ^ K • v ∈ sm (X ^ M) (L.N c))
    (h7 : ∀ (K : ℕ), ∀ v ∈ L.pull c j, B.lc ^ K • v ∈ sm (B.ff j M g) (L.pull c j) →
      v ∈ sm (B.ff j M g) (L.pull c j))
    (h : L.IsTr c j M g sig 0 τ) : τ ∈ sm (B.ff j M g) (L.pull c j) := by
  obtain ⟨hτ, K, v, hv, hz, hf⟩ := h
  rw [smul_zero, sub_zero] at hz
  obtain ⟨K', hK'⟩ := h6 v hv hz
  have h1 : L.phiIt c j (B.lc ^ K' • v) ∈ sm (B.ff j M g) (L.pull c j) := phiIt_XM L c j M h3 hK'
  rw [phiIt_lc] at h1
  refine h7 (K' + K) τ hτ ?_
  have e : B.lc ^ (K' + K) • τ =
      B.lc ^ K' • (B.lc ^ K • τ - B.lc ^ sig • L.phiIt c j v) +
        B.lc ^ sig • (B.lc ^ K' • L.phiIt c j v) := by
    rw [pow_add]
    simp only [smul_sub, smul_smul, mul_comm]
    abel
  rw [e]
  exact add_mem (Submodule.smul_mem _ _ hf) (Submodule.smul_mem _ _ h1)

theorem cobound_of_small {M : ℕ} (hX : B.γ X ∈ Ideal.span {(X : PowerSeries O)})
    (h1 : ∀ i, ∀ v ∈ L.N i, L.γ i v - v ∈ sm X (L.N i))
    (h3 : ∀ t : ZMod n → V, (∀ i, t i ∈ sm (X ^ M) (L.N i)) →
      ∃! z : ZMod n → V, (∀ i, z i ∈ sm (X ^ M) (L.N i)) ∧ L.dφ z = t)
    {y z : ZMod n → V} (hc : L.IsCocycle y z) (hy : ∀ i, y i ∈ sm (X ^ M) (L.N i))
    (hz : ∀ i, z i ∈ sm (X ^ M) (L.N i)) : L.IsCobound y z := by
  obtain ⟨m, ⟨hm, hmy⟩, -⟩ := h3 y hy
  refine ⟨m, hmy.symm, ?_⟩
  have hγ : ∀ i, L.dγ m i ∈ sm (X ^ M) (L.N i) := by
    intro i
    show L.γ i (m i) - m i ∈ _
    exact sub_mem (γ_sm L (γ_pow_span hX M) (fun v hv => gam_N L h1 i hv) (hm i)) (hm i)
  have hc' : L.dγ y = L.dφ z := hc
  have h0 : ∀ i, (0 : ZMod n → V) i ∈ sm (X ^ M) (L.N i) := fun i => zero_mem _
  obtain ⟨u, -, hu⟩ := h3 0 h0
  have e1 : z - L.dγ m = u :=
    hu _ ⟨fun i => sub_mem (hz i) (hγ i), by rw [dφ_sub, dφ_dγ, hmy, hc', sub_self]⟩
  have e2 : (0 : ZMod n → V) = u :=
    hu _ ⟨h0, by funext i; simp only [Lat.dφ, Pi.zero_apply, map_zero, sub_zero]⟩
  rw [← e2, sub_eq_zero] at e1
  exact e1

end lat

section hom
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V V' : Type} [AddCommGroup V]
  [Module (PowerSeries O) V] [AddCommGroup V'] [Module (PowerSeries O) V']
  {L : Lat B n V} {L' : Lat B n V'} (h : LatHom L L')

theorem hom_sm {a : PowerSeries O} {S : Submodule (PowerSeries O) V}
    {S' : Submodule (PowerSeries O) V'} (hS : ∀ v ∈ S, h.f v ∈ S') {v : V} (hv : v ∈ sm a S) :
    h.f v ∈ sm a S' := by
  obtain ⟨u, hu, rfl⟩ := mem_sm.1 hv
  rw [map_smul]
  exact smul_mem_sm a (hS u hu)

theorem hom_isTr {c : ZMod n} {j M g sig : ℕ} {z τ : V} (ht : L.IsTr c j M g sig z τ) :
    L'.IsTr c j M g sig (h.f z) (h.f τ) := by
  obtain ⟨hτ, K, v, hv, hz, hf⟩ := ht
  refine ⟨hom_pull h c j hτ, K, h.f v, hom_sm h (fun u hu => h.map_N c u hu) hv, ?_, ?_⟩
  · have := hom_sm h (fun u hu => h.map_N c u hu) hz
    simpa only [map_sub, map_smul, h.γ_comm] using this
  · have := hom_sm h (fun u hu => hom_pull h c j hu) hf
    simpa only [map_sub, map_smul, hom_phiIt] using this

end hom

end IdempotentNormalFormsRhoFacts

open S1 IdempotentNormalFormsRhoFacts

theorem rho_map_functorial : RhoFun := by
  unfold RhoFun
  intro O _ B n _ j M g sig V V' _ _ _ _ L L' h c w y z hr
  obtain ⟨τ, hτ, hy, hc, hz⟩ := hr
  refine ⟨h.f τ, ?_, ?_, ?_, fun i => hom_sm h (fun u hu => h.map_N i u hu) (hz i)⟩
  · have := hom_isTr h hτ
    simpa only [map_sub, h.γ_comm] using this
  · funext i
    rw [hy]
    by_cases hi : i = c + (j : ZMod n)
    · subst hi
      simp only [Pi.single_eq_same, map_sub, map_smul, hom_phiIt]
    · simp only [Pi.single_eq_of_ne hi, map_zero]
  · have hc' : L.dγ y = L.dφ z := hc
    show L'.dγ _ = L'.dφ _
    funext i
    have e := congrArg h.f (congrFun hc' i)
    simpa only [Lat.dγ, Lat.dφ, map_sub, h.γ_comm, h.φ_comm] using e

theorem rho_map_exists : RhoExists := by
  unfold RhoExists
  intro O _ B n _ Cu j M g sig V _ _ L hB hL c hc w hw
  have ⟨_, _, h3, _, h5, _, _, _⟩ := hL
  have hw' : L.γ c w - w ∈ sm X (L.N c) := hw
  obtain ⟨τ, hτ⟩ := h5 c hc _ hw'
  have hR : L.γ (c + (j : ZMod n)) (B.lc ^ sig • L.phiIt c j w - τ) -
      (B.lc ^ sig • L.phiIt c j w - τ) ∈ sm (X ^ M) (L.N (c + (j : ZMod n))) := by
    have e : L.γ (c + (j : ZMod n)) (B.lc ^ sig • L.phiIt c j w - τ) -
        (B.lc ^ sig • L.phiIt c j w - τ) =
        B.lc ^ sig • L.phiIt c j (L.γ c w - w) - (L.γ (c + (j : ZMod n)) τ - τ) := by
      simp only [map_sub, gam_lc_smul, gam_phiIt L c _ j rfl, phiIt_sub, smul_sub]
      abel
    rw [e]
    exact gamR_mem L hB hL hc hw' hτ
  have ht : ∀ i, L.dγ (Pi.single (c + (j : ZMod n)) (B.lc ^ sig • L.phiIt c j w - τ)) i ∈
      sm (X ^ M) (L.N i) := by
    intro i
    rw [dγ_single]
    by_cases hi : i = c + (j : ZMod n)
    · subst hi
      rw [Pi.single_eq_same]
      exact hR
    · rw [Pi.single_eq_of_ne hi]
      exact zero_mem _
  obtain ⟨z, ⟨hz, hzt⟩, -⟩ := h3 _ ht
  exact ⟨Pi.single (c + (j : ZMod n)) (B.lc ^ sig • L.phiIt c j w - τ), z, τ, hτ, rfl,
    hzt.symm, hz⟩

theorem rho_map_linear : RhoLin := by
  unfold RhoLin
  intro O _ B n _ Cu j M g sig V _ _ L hB hL c hc m w w' y z y' z' hr hr' hu
  obtain ⟨h1, -, h3, h4, -, h6, h7, -⟩ := hL
  obtain ⟨τ, hτ, hy, hcy, hz⟩ := hr
  obtain ⟨τ', hτ', hy', hcy', hz'⟩ := hr'
  have hT := isTr_sub (isTr_self j M g sig hu) (isTr_sub hτ' (isTr_C m hτ))
  have e0 : L.γ c (w' - C m • w) - (w' - C m • w) -
      ((L.γ c w' - w') - C m • (L.γ c w - w)) = 0 := by
    simp only [map_sub, γ_C, smul_sub]
    abel
  rw [e0] at hT
  have hmem := isTr_zero hB.2.2 (h6 c hc) (h7 c hc) hT
  have hR : (B.lc ^ sig • L.phiIt c j w' - τ') - C m • (B.lc ^ sig • L.phiIt c j w - τ) ∈
      sm (X ^ M) (L.N (c + (j : ZMod n))) := by
    have e : (B.lc ^ sig • L.phiIt c j w' - τ') - C m • (B.lc ^ sig • L.phiIt c j w - τ) =
        B.lc ^ sig • L.phiIt c j (w' - C m • w) - (τ' - C m • τ) := by
      simp only [phiIt_sub, phiIt_C, smul_sub, smul_smul, mul_comm]
      abel
    rw [e]
    exact h4 c hc hmem
  apply cobound_of_small hB.1 h1 h3
  · have a : L.dγ y = L.dφ z := hcy
    have a' : L.dγ y' = L.dφ z' := hcy'
    show L.dγ (y' - C m • y) = L.dφ (z' - C m • z)
    rw [dγ_sub, dγ_C, dφ_sub, dφ_C, a, a']
  · intro i
    rw [hy, hy']
    by_cases hi : i = c + (j : ZMod n)
    · subst hi
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same]
      exact hR
    · simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero, sub_zero]
      exact zero_mem _
  · intro i
    exact sub_mem (hz' i) (Submodule.smul_mem _ _ (hz i))

end Formalism.ExponentWindows.E
