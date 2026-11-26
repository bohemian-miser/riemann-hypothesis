module

public import New.Congruences.Lifting.DeepPoints

/-!
# Few low jumps: length lost to depth and a submodule cupping to zero

For a side `S` (`New.Lift.KummerChart.PairingSide`), orders and depths are functions `o l u` of a
level `l` and a line `u`. The level `0` belongs to the prime `E` of the chart `k`.
`New.relLength S T` is the length of `S / (S ⊓ T)`. A point `x` of the extension lies in
`S.deepElements i c` if it lies over a constant at `i` and has the depth `c`: the differences
`g • x - x` have exponents `c` for all `g` in the subgroup `Γ'` of the chart. On an unramified
chart, this file bounds the length lost when the depth is raised, for a side with few jumps in the
low window. It concludes that most constants have deep points above them, and that these constants
satisfy the cup conditions with exponent `0`.

## Main definitions and results

* `New.Lift.KummerChart.PairingSide.deepConstants`: the constants below the points of the extension
  with a given pole order and depth.
* `New.Lift.KummerChart.PairingSide.exists_relLength_le_and_isScaledCupCoboundary`: the submodule of
  bounded colength that cups to zero.

Notions from other files:
* `New.Lift.KummerChart`: a Kummer chart `k` of the group `Γ` over `G_p`: a ring `Λ⟦z⟧` inside
  `A_inf` with a distinguished element `E` (`E = z + p` if the chart is unramified) and a subgroup
  `Γ'` of `Γ` of index prime to `p`. Its letters are the units of the residue field
  `𝔽_{p ^ k.f}`; a letter singles out embeddings of the coefficients, and `i.stepBack l` is the
  letter `l` steps of Frobenius before `i`.
* `New.Lift.KummerChart.PairingSide`: one side of a pairing: lattices `Y` and `paramLattice`, an
  `O`-linear map `cocycleMap` from `paramLattice` to the crystalline cocycles `Z_f(Y)`, and for each
  letter a finite set of integers that contains `0`. `S.extensionLattice` is the extension of the
  trivial lattice `paramLattice` by `Y` given by the cocycles of `S`, with the jump sets of `S`.
* Orders `o l u` prescribe, for every level `l` and jump `u` at `i.stepBack l`, a power of the
  uniformiser of `B_dR⁺` that divides the value of an element on the line `u` at the level `l`. An
  element has depth `o` if its differences with its translates by `Γ'` have orders `o`.
* `New.Lift.KummerChart.cost`: the cost `k.cost l n = v_p(n) + d + 3 l` of the step `n` at the level
  `l`, with `v_p(0) = 0`; here `d = 0` if the index `e` of the chart is `1`, and `d = v_p(e) + 1`
  otherwise.
* `New.Lift.KummerChart.PairingSide.KillsCokernel`: `p ^ κ * E ^ a` kills the cokernel at the letter
  `i`: it multiplies the letter-`i` part of `A_inf ⊗ C` into the image of the extension's module of
  standard exponents of level `0`.
* `New.Lift.FitsWindows`: `FitsWindows η ε b W U` says that `U` lies in the union of the low window
  `[-η, η]` and the far window `ε • [b, b + W]`.
* `New.Lift.Pairing.IsScaledCupCoboundary`: the cup conditions with exponent `H` for `c` and `c'`:
  the cup product of the cocycles `S.cocycleMap c` and `p ^ H • S'.cocycleMap c'` is a continuous
  coboundary.

## Relation to the literature

See `New.Congruences.Lifting.CutExponentBounds` and `New.Congruences.Lifting.CupOrthogonalityBounds`
for related work.
-/

@[expose] public section

section FewLowJumps

namespace New.Lift.KummerChart.PairingSide

open Submodule Finset JumpLattice Period Int

variable {p : ℕ} [ThePrime p] [Γ : GroupOverGp p]

section DeepConstants

variable {k : KummerChart Γ} {O : k.Coeffs}

/-- The constants below the points of the extension with a pole of order at most `-t` and depth `c`
at the letter `i`: the image under `S.localizedProjTrivial` of the elements of `S.deepElements i c`
that lie in the Kisin part with exponents `raisedOrdersAtZero t` (`t - u` at the level `0`, `-u`
beyond). -/
noncomputable def deepConstants (S : PairingSide O) (i : Letter) (t : ℤ) (c : ℕ → ℤ → ℤ) :
    Submodule ℤ_[p] (Ambient (k := k) (O := O) (L := S.trivialLattice)) :=
  (locKisinPart (S.extensionLattice.withOrders i (raisedOrdersAtZero t)) ⊓ S.deepElements i c).map
    S.localizedProjTrivial

/-- The depth used at a letter whose far window `-[b, b + W]` is negative, as a function of the
level `l` and the line `u`: the constant `b + W + a + η` at the level `0`, `W + 1 - u` at the level
`1` (plus `2a` on the low lines `|u| ≤ η`), and `-u` beyond. -/
def negativeWindowDepth (a η W b : ℕ) (l : ℕ) (u : ℤ) : ℤ :=
  if l = 0 then b + W + a + η
  else if l = 1 then W + 1 - u + (if |u| ≤ η then 2 * a else 0)
  else -u

/-- The depth used at a letter whose far window is `ε [b, b + W]`: it is
`raisedOrdersAtZero (2a + η)` if `ε = 1` and `negativeWindowDepth a η W b` if `ε = -1`. -/
def fewLowJumpsDepth (a η W b : ℕ) (ε : ℤˣ) : ℕ → ℤ → ℤ :=
  if ε = 1 then raisedOrdersAtZero (2 * a + η) else negativeWindowDepth a η W b

variable {S : k.PairingSide O} {i : k.Letter} {c : ℕ → ℤ → ℤ}

/-- A point lies in the Kisin part of `S.kerWithOrders i c` if and only if it has the exponents
`c` at the letter `i` and lies over `0`. -/
lemma mem_locKisinPart_kerWithOrders_iff {x : S.extensionLattice.kisinLoc} :
    x ∈ locKisinPart (S.kerWithOrders i c) ↔
      (x : S.extensionLattice.Ambient) ∈ S.extensionLattice.withOrders i c ∧ S.projTrivial.wittMap x
        = 0 :=
  Iff.rfl

/-- A point `x` of `S.extensionLattice.kisinLoc` lies in `S.deepElements i c` if and only if two
things hold. First, `S.localizedProjTrivial x` lies in the range of `S.constantAt i`. Second, `x`
lies in `invariantsMod (S.extensionLattice.withOrders i c)`: for every `g` in `Γ'`, `g x - x` has
orders `c` at the letter `i`. -/
lemma mem_deepElements_iff_mem_range_and_invariantsMod {x : S.extensionLattice.kisinLoc} :
    x ∈ S.deepElements i c ↔
      S.localizedProjTrivial x ∈ (S.constantAt i).range ∧
      (x : S.extensionLattice.Ambient) ∈ invariantsMod (S.extensionLattice.withOrders i c) :=
  Iff.rfl

/-- On an unramified chart, where `E = z + p`, the element `φ ^ a E` is congruent to `E ^ p ^ a`
modulo `p`. -/
lemma natCast_dvd_frobE_zero_pow_sub_frobE (hk : k.IsUnramified) (a : ℕ) :
    (p : k.S) ∣ k.frobE 0 ^ p ^ a - k.frobE a := by
  obtain ⟨hE, -, -⟩ := hk
  simpa [k.dvd_iff_coe_dvd, val_frobE, hE, phi_pow_smul_z, ← sub_sub, dvd_sub_left] using
    sub_dvd_pow_sub_pow (k.z + p) k.z (p ^ a)

/-- Let `S` be a side on an unramified chart and `i` a letter, and suppose that no multiple of `p`
lies strictly between `c 0 v` and `c 0 v + N` for any `v`. Then some operator `A` of cost `0` on the
points of the extension (one with `A w - w` over the constant `0` and with orders `o` whenever `w`
has depth `o`) takes `S.deepElements i` for `c` raised by `1` at the level `0`, that is the
elements over constants at `i` of this depth, into those for `c` raised by `N` at the level `0`. -/
lemma exists_isOperatorOfCost_zero_mem_deepElements (hk : k.IsUnramified) {N : ℤ}
    (h_free : ∀ v : ℤ, ∀ n ∈ Ioo (c 0 v) (c 0 v + N), ¬(p : ℤ) ∣ n) :
    ∃ A : S.extensionLattice.kisinLoc →+ S.extensionLattice.kisinLoc, S.IsOperatorOfCost 0 A ∧
      ∀ w ∈ S.deepElements i (raiseOrdersAt c 0),
        A w ∈ S.deepElements i fun (l : ℕ) (v : ℤ) ↦ c l v + if 0 = l then N else 0 := by
  let steps : Finset ℤ := (S.jumpSet i).biUnion fun v ↦ Ioo (c 0 v) (c 0 v + N)
  obtain ⟨A, h_reach, h_raise⟩ := S.exists_isOperatorOfCost_and_mem_deepElements
    (({0} : Finset ℕ).sigma fun _ ↦ steps)
  have h_cost : ∑ q ∈ ({0} : Finset ℕ).sigma fun _ ↦ steps, k.cost q.1 q.2 = 0 := by
    rw [sum_sigma, sum_singleton]
    refine sum_eq_zero fun n hn ↦ ?_
    obtain ⟨v, -, hn_mem⟩ := mem_biUnion.1 hn
    exact Nat.le_zero.1 (cost_le_of_isUnramified hk fun h ↦ (h_free v n hn_mem h).elim)
  refine ⟨A, by rwa [h_cost] at h_reach, fun w hw ↦ h_raise hw _ fun l v hv n hn_ge hn_lt ↦ ?_⟩
  obtain rfl : l = 0 := by
    by_contra h; simp only [raiseOrdersAt, Ne.symm h, ↓reduceIte] at hn_ge hn_lt; omega
  simp only [raiseOrdersAt, ↓reduceIte] at hn_ge hn_lt
  exact mem_sigma.2 ⟨mem_singleton_self 0,
    mem_biUnion.2 ⟨v, hv, mem_Ioo.2 ⟨by dsimp at *; omega, by dsimp at *; omega⟩⟩⟩

/-- Division by `p`. Suppose the chart is unramified, and no multiple of `p` lies strictly between
`c 0 v` and `c 0 v + p ^ a` for any `v`. Let `x` have depth `c`, and let `w` lie over `0` with
orders `c` raised by `1` at the level `0`. If `p • x - w` has the depth `raiseOrder c a u` (`c` with
the value `c a u` raised by `1`), then so has `x - m` for some `m` over `0` with orders `c`. -/
lemma exists_sub_mem_deepElements_of_smul_sub_mem (hk : k.IsUnramified) {a : ℕ} {u : ℤ}
    {x w : S.extensionLattice.kisinLoc}
    (h_free : ∀ v : ℤ, ∀ n ∈ Ioo (c 0 v) (c 0 v + p ^ a), ¬(p : ℤ) ∣ n)
    (hx : x ∈ S.deepElements i c) (hw : w ∈ locKisinPart (S.kerWithOrders i (raiseOrdersAt c 0)))
    (h_deep : (p : ℤ_[p]) • x - w ∈ S.deepElements i (raiseOrder c a u)) :
    ∃ m ∈ locKisinPart (S.kerWithOrders i c),
      x - m ∈ S.deepElements i (raiseOrder c a u) := by
  -- Write `E = k.frobE 0`. An operator `A` of cost `0` gives `A w = E ^ p ^ a • w'`, where `w'`
  -- lies over `0` and has exponents `c`. As `E ^ p ^ a = k.frobE a + p r`, this gives
  -- `A w = k.frobE a • w' + p r w'`, and `A x - r w'` has the depth `raiseOrder c a u`.
  obtain ⟨A, h_reach, h_raise⟩ := exists_isOperatorOfCost_zero_mem_deepElements (S := S) (i := i) hk
    h_free
  have hw_deep := locKisinPart_kerWithOrders_le_deepElements hw
  obtain ⟨hAw_exp, hAw_ker⟩ :=
    mem_locKisinPart_kerWithOrders_iff.1 (h_reach.apply_mem_of_kerWithOrders_le le_rfl hw hw_deep)
  obtain ⟨-, hAw_inv⟩ := h_raise w hw_deep
  let w' : S.extensionLattice.kisinLoc :=
    ⟨k.frobEUnit 0 ^ (-p ^ a : ℤ) • (A w : S.extensionLattice.Ambient),
      frobEUnit_zpow_smul_mem_kisinLoc_iff.mpr (A w).prop⟩
  have hw'_exp : (w' : S.extensionLattice.Ambient) ∈ S.extensionLattice.withOrders i c := by
    refine frobEUnit_zpow_smul_mem_withOrders 0 (-p ^ a)
      (mem_withOrders_improvedOrders hAw_exp hAw_inv) fun l v _ ↦ ?_
    -- `0` is not among the steps, so the depth of `A w` gives it the same exponents.
    have h_zero : 0 ∉ Ioo (c 0 v) (c 0 v + p ^ a) := fun h ↦ h_free v 0 h (dvd_zero _)
    simp only [improvedOrders, raiseOrdersAt, mem_Ioo] at h_zero ⊢
    obtain rfl | hl := eq_or_ne 0 l <;> omega
  obtain ⟨r, hr⟩ := natCast_dvd_frobE_zero_pow_sub_frobE hk a
  let m : S.extensionLattice.kisinLoc := r • w' - (A x - p ^ 0 • x)
  have hm : m ∈ locKisinPart (S.kerWithOrders i c) :=
    sub_mem ⟨smul_mem _ r.val hw'_exp, by simp [w', hAw_ker]⟩ (h_reach hx)
  obtain ⟨h_const, h_inv⟩ : x - m ∈ S.deepElements i c :=
    sub_mem hx (locKisinPart_kerWithOrders_le_deepElements hm)
  have h_smul_inv : (↑(p • (x - m)) : S.extensionLattice.Ambient) ∈
      invariantsMod (S.extensionLattice.withOrders i (raiseOrder c a u)) := by
    obtain ⟨-, h_deep_inv⟩ := h_reach.apply_mem_of_kerWithOrders_le
      locKisinPart_kerWithOrders_le_deepElements h_deep h_deep
    have h_eq : p • (x - m) = A ((p : ℤ_[p]) • x - w) + (A w - p • r • w') := by
      simp only [m, Nat.cast_smul_eq_nsmul, map_sub, map_nsmul, pow_zero, one_smul, smul_sub]; abel
    have hAw_sub : (↑(A w - p • r • w') : S.extensionLattice.Ambient) =
        k.frobEUnit a ^ (1 : ℤ) • (w' : S.extensionLattice.Ambient) := by
      rw [Submodule.coe_sub, show (A w : S.extensionLattice.Ambient) =
          k.frobE 0 ^ p ^ a • (w' : S.extensionLattice.Ambient) by
        simp [w', smul_eq_val_smul, ← frobEUnit_pow_smul, ← zpow_natCast (k.frobEUnit 0)],
        eq_add_of_sub_eq' hr]
      simp [smul_eq_val_smul, add_smul, mul_smul, Nat.cast_smul_eq_nsmul, -map_smul]
    rw [h_eq, Submodule.coe_add, hAw_sub]
    exact add_mem h_deep_inv (smul_sub_mem_withOrders
      (frobEUnit_zpow_smul_mem_withOrders a 1 hw'_exp fun l v _ ↦ by
        simp only [raiseOrder]; split_ifs <;> omega))
  -- No `φ ^ l E` divides `p`, so the factor `p` can be cancelled.
  refine ⟨m, hm, h_const, fun g ↦
    mem_withOrders_of_smul not_frobE_dvd_p (withOrders_le_kisinLocAinf (h_inv g)) ?_⟩
  -- The action of `g` commutes with the multiplication by `p`.
  rw [Nat.cast_smul_eq_nsmul, smul_sub, ← smul_comm g, ← map_nsmul]
  exact h_smul_inv g

/-- There is an operator `A` on `S.extensionLattice.kisinLoc` whose cost is `k.cost a (c a u)`, the
cost of the step `(a, c a u)`. It maps `S.deepElements i c` into
`S.deepElements i (raiseOrder c a u)`, so it improves the depth from `c` to `raiseOrder c a u`,
which is `c` with the value `c a u` raised by `1`. -/
lemma exists_isOperatorOfCost_mem_deepElements_raiseOrder (a : ℕ) (u : ℤ) :
    ∃ A : S.extensionLattice.kisinLoc →+ S.extensionLattice.kisinLoc,
      S.IsOperatorOfCost (k.cost a (c a u)) A ∧
      ∀ x ∈ S.deepElements i c, A x ∈ S.deepElements i (raiseOrder c a u) := by
  obtain ⟨A, h_reach, h_raise⟩ := S.exists_isOperatorOfCost_and_mem_deepElements {⟨a, c a u⟩}
  refine ⟨A, by simpa using h_reach, fun x hx ↦ h_raise hx _ fun l v _ n hn_ge hn_lt ↦ ?_⟩
  simp only [raiseOrder, mem_singleton, Sigma.mk.inj_iff, heq_eq_eq] at hn_lt ⊢
  split_ifs at hn_lt with h
  · rcases h with ⟨rfl, rfl⟩; exact ⟨rfl, by omega⟩
  · omega

/-- A primitive relation for one step. Let `S` be a side on an unramified chart `k` and `i` a
letter. Let `c a u < c a v` for the jumps `v < u` at `i.stepBack a`, and let no multiple of `p` lie
strictly between `c 0 v` and `c 0 v + p ^ a`. Take one more point `x j` of depth `c` than the
residue degree `k.f` times the multiplicity of the jump `u` there, such that each `p • x j` is the
sum of an element of depth `raiseOrder c a u` and one over `0` with orders `c`. Then a combination
of the `x j` with one coefficient equal to `1` is such a sum as well. -/
lemma exists_sum_smul_sub_mem_deepElements (hk : k.IsUnramified) {a : ℕ} {u : ℤ}
    (h_free : ∀ v : ℤ, ∀ n ∈ Ioo (c 0 v) (c 0 v + p ^ a), ¬(p : ℤ) ∣ n)
    (h_ord : ∀ v ∈ S.jumpSet (i.stepBack a), v < u → c a u < c a v)
    (x : Fin (k.f * S.jumpMultiplicity (i.stepBack a) u + 1) → S.extensionLattice.kisinLoc)
    (hx : ∀ j : Fin (k.f * S.jumpMultiplicity (i.stepBack a) u + 1), x j ∈ S.deepElements i c)
    (h_split : ∀ j : Fin (k.f * S.jumpMultiplicity (i.stepBack a) u + 1),
      ∃ x' ∈ S.deepElements i (raiseOrder c a u),
        ∃ m ∈ locKisinPart (S.kerWithOrders i c), x' + m = (p : ℤ_[p]) • x j) :
    ∃ β : Fin (k.f * S.jumpMultiplicity (i.stepBack a) u + 1) → ℤ_[p],
      (∃ j : Fin (k.f * S.jumpMultiplicity (i.stepBack a) u + 1), β j = 1) ∧
      ∃ m ∈ locKisinPart (S.kerWithOrders i c),
        ∑ j, β j • x j - m ∈ S.deepElements i (raiseOrder c a u) := by
  -- Write `p • x j = x' j + m j`, where `m j` is the image of a vector `y j` of the sublattice. A
  -- primitive combination of the `y j` is `w + z`, where `w` has the orders `c` raised by `1` at
  -- the level `0` and `z` has the orders `raiseOrder c a u`. Then divide by `p`.
  choose x' hx' m hm h_split using h_split
  choose y hy_exp hy_incl hy_mem using fun j ↦ exists_inclKer_eq_of_kerWithOrders (hm j)
  obtain ⟨β, j, hβ_one, h_comb⟩ := exists_sum_smul_mem_locKisinPart_sup c hk a i le_rfl h_ord
    (fun j ↦ ⟨y j, hy_mem j (m j).prop⟩) hy_exp
  obtain ⟨w, hw, z, hz, h_wz⟩ := mem_sup.mp h_comb
  let w' : S.extensionLattice.kisinLoc :=
    ⟨S.inclKer.wittMap w, S.inclKer.wittMap_mem_kisinLoc w.prop⟩
  have hw' : w' ∈ locKisinPart (S.kerWithOrders i (raiseOrdersAt c 0)) :=
    ⟨S.inclKer.wittMap_mem_withOrders le_rfl hw, by simp [w']⟩
  have h_sum_deep : ∑ j, β j • x j ∈ S.deepElements i c := sum_smul_mem _ β fun j _ ↦ hx j
  have h_deep : (p : ℤ_[p]) • ∑ j, β j • x j - w' ∈ S.deepElements i (raiseOrder c a u) := by
    -- `p • ∑ j, β j • x j - w'` is the sum of `∑ j, β j • x' j` and the image of `z`.
    have h_sum : ∑ j, β j • (x' j : S.extensionLattice.Ambient) + S.inclKer.wittMap z ∈
        invariantsMod (S.extensionLattice.withOrders i (raiseOrder c a u)) :=
      (invariantsMod _).add_mem (sum_smul_mem _ β fun j _ ↦ (hx' j).2)
        (smul_sub_mem_withOrders (S.inclKer.wittMap_mem_withOrders le_rfl hz))
    refine ⟨sub_mem (smul_mem _ _ h_sum_deep.1) (locKisinPart_kerWithOrders_le_deepElements hw').1,
      ?_⟩
    -- The option makes the definitional steps explicit, which keeps the kernel check short.
    simpa -implicitDefEqProofs [w', eq_sub_of_add_eq' h_wz, smul_sum, smul_comm _ (β _),
      ← h_split, hy_incl, add_sub, sum_add_distrib] using h_sum
  exact ⟨β, ⟨j, hβ_one⟩, exists_sub_mem_deepElements_of_smul_sub_mem hk h_free h_sum_deep hw'
    h_deep⟩

/-- One step. Let `S` be a side on an unramified chart `k`, `i` a letter, and
`S.deepConstants i 0 c` the constants at `i` below elements of the extension without pole and of
depth `c`. Let `c l v ≥ -v` for the jumps `v` at `i.stepBack l`, let `c a u < c a v` for the jumps
`v < u` at `i.stepBack a`, and let no multiple of `p` lie strictly between `c 0 v` and
`c 0 v + p ^ a`. Raising `c a u` by `1` shrinks these constants by a module whose length
(`relLength`) is at most the cost `k.cost a (c a u) = v_p(c a u) + 3 a` of the step times the
residue degree `k.f` times the multiplicity of the jump `u` at `i.stepBack a`. -/
lemma relLength_deepConstants_raiseOrder_le (hk : k.IsUnramified) {a : ℕ} {u : ℤ}
    (h_free : ∀ v : ℤ, ∀ n ∈ Ioo (c 0 v) (c 0 v + p ^ a), ¬(p : ℤ) ∣ n)
    (hc_ge : ∀ l : ℕ, ∀ v ∈ S.jumpSet (i.stepBack l), -v ≤ c l v)
    (h_ord : ∀ v ∈ S.jumpSet (i.stepBack a), v < u → c a u < c a v) :
    relLength (S.deepConstants i 0 c) (S.deepConstants i 0 (raiseOrder c a u)) ≤
      (k.cost a (c a u) * (k.f * S.jumpMultiplicity (i.stepBack a) u) : ℕ) := by
  -- Let `X o` be the points without pole of depth `o`, and `M` the points over `0` with exponents
  -- `c`. The quotient of `X c` by `X c_raised ⊔ M` is killed by `p` to the cost of the step, and
  -- any `k.f * S.jumpMultiplicity (i.stepBack a) u + 1` of its elements killed by `p` satisfy a
  -- primitive relation.
  let X (o : ℕ → ℤ → ℤ) : Submodule ℤ_[p] S.extensionLattice.kisinLoc :=
    locKisinPart (S.extensionLattice.withOrders i (raisedOrdersAtZero 0)) ⊓ S.deepElements i o
  let M : Submodule ℤ_[p] S.extensionLattice.kisinLoc := locKisinPart (S.kerWithOrders i c)
  have hM_no_pole : M ≤ locKisinPart (S.extensionLattice.withOrders i (raisedOrdersAtZero 0)) :=
    fun _ ⟨hm, _⟩ ↦ mem_withOrders_of_le hm fun l v hv ↦ by
      simpa [raisedOrdersAtZero] using hc_ge l v hv
  -- `M` lies over the constant `0`, so it is enough to compare `X c` with `X c_raised ⊔ M`.
  have h_const : relLength (S.deepConstants i 0 c) (S.deepConstants i 0 (raiseOrder c a u)) ≤
      relLength (X c) (X (raiseOrder c a u) ⊔ M) := by
    rw [deepConstants, deepConstants, ← relLength_comap, comap_map_eq]
    exact relLength_mono le_rfl (sup_le_sup_left (fun _ ⟨_, h_ker⟩ ↦ h_ker) _)
  refine h_const.trans (relLength_le_of_relations _ (fun x ⟨hx, hx_deep⟩ ↦ ?_) fun x hx ↦ ?_)
  · -- An operator `A` makes `x` deeper at the cost of the step, and `A x - p ^ cost • x ∈ M`.
    obtain ⟨A, h_reach, h_raise⟩ := exists_isOperatorOfCost_mem_deepElements_raiseOrder (S := S) a u
    exact mem_sup.mpr ⟨A x, ⟨h_reach.apply_mem_of_kerWithOrders_le hM_no_pole hx hx_deep,
      h_raise x hx_deep⟩, _, neg_mem (h_reach hx_deep), by simp⟩
  · choose hx_no_pole hx_deep using fun j ↦ mem_inf.1 (hx j).1
    obtain ⟨β, ⟨j, hβ_one⟩, m, hm, h_sub⟩ := exists_sum_smul_sub_mem_deepElements hk h_free h_ord x
      hx_deep fun j ↦ (mem_sup.mp (hx j).2).imp fun _ ⟨hx', h⟩ ↦ ⟨hx'.2, h⟩
    exact ⟨β, j, hβ_one, mem_sup.mpr ⟨_, ⟨sub_mem (sum_smul_mem _ β fun j _ ↦ hx_no_pole j)
      (hM_no_pole hm), h_sub⟩, m, hm, sub_add_cancel _ m⟩⟩

/-- Raising `c a u` by `1` removes the step `⟨u, c a u⟩` from the steps `⟨v, n⟩` with `v ∈ U` and
`c a v ≤ n < d v`. -/
lemma sigma_Ico_raiseOrder (U : Finset ℤ) (a : ℕ) (u : ℤ) (d : ℤ → ℤ) :
    (U.sigma fun v : ℤ ↦ Ico (raiseOrder c a u a v) (d v)) =
      (U.sigma fun v : ℤ ↦ Ico (c a v) (d v)).erase ⟨u, c a u⟩ := by
  ext ⟨v, n⟩
  simp only [mem_sigma, mem_Ico, mem_erase, ne_eq, Sigma.mk.inj_iff, heq_eq_eq, raiseOrder,
    true_and]
  split_ifs <;> grind

/-- All steps at one level. Let `S` be a side on an unramified chart `k`, `i` a letter, and
`S.deepConstants i 0 c` the constants at `i` below elements of the extension without pole and of
depth `c`. Suppose no multiple of `p` lies strictly between `c 0 v` and `c 0 v + p ^ a`,
`c l u ≥ -u` on the jumps `u ∈ S.jumpSet (i.stepBack l)`, and `c' ≤ c` there for `l ≠ a`. If `c' a`
is antitone on the jumps at `i.stepBack a`, then the quotient of these constants by those of depth
`c'` has length at most the sum, over the steps `⟨u, n⟩` with `c a u ≤ n < c' a u`, of the cost
`k.cost a n = v_p(n) + 3 a` times the residue degree `k.f` times the multiplicity of the jump
`u`. -/
lemma relLength_deepConstants_le_sum_cost (hk : k.IsUnramified) {a : ℕ} {c' : ℕ → ℤ → ℤ}
    (h_free : ∀ v : ℤ, ∀ n ∈ Ioo (c 0 v) (c 0 v + p ^ a), ¬(p : ℤ) ∣ n)
    (hc_ge : ∀ l : ℕ, ∀ u ∈ S.jumpSet (i.stepBack l), -u ≤ c l u)
    (hc'_le : ∀ l : ℕ, l ≠ a → ∀ u ∈ S.jumpSet (i.stepBack l), c' l u ≤ c l u)
    (h_anti : AntitoneOn (c' a) (S.jumpSet (i.stepBack a))) :
    relLength (S.deepConstants i 0 c) (S.deepConstants i 0 c') ≤
      (∑ s ∈ (S.jumpSet (i.stepBack a)).sigma fun u : ℤ ↦ Ico (c a u) (c' a u),
        k.cost a s.snd * (k.f * S.jumpMultiplicity (i.stepBack a) s.fst) : ℕ) := by
  -- Induct on the set of steps left, taking the first step on the least line that is not yet at
  -- its target.
  induction' h_steps : (S.jumpSet (i.stepBack a)).sigma fun u ↦ Ico (c a u) (c' a u)
    using eraseInduction with I ih generalizing c
  subst h_steps
  by_cases! h_left : ∀ v ∈ S.jumpSet (i.stepBack a), c' a v ≤ c a v
  · -- No step is left: the depth `c` implies the depth `c'`.
    have h_le : S.deepElements i c ≤ S.deepElements i c' :=
      fun _ ⟨h_const, h_inv⟩ ↦ ⟨h_const, fun g ↦ mem_withOrders_of_le (h_inv g) fun l v hv ↦
        (eq_or_ne l a).elim (fun h ↦ h ▸ h_left v (h ▸ hv)) fun hl ↦ hc'_le l hl v hv⟩
    exact (relLength_eq_zero.2 (map_mono (inf_le_inf_left _ h_le))).trans_le bot_le
  obtain ⟨u, ⟨hu, hu_lt⟩, h_min⟩ : ∃ u : ℤ, (u ∈ S.jumpSet (i.stepBack a) ∧ c a u < c' a u) ∧
      ∀ v ∈ S.jumpSet (i.stepBack a), c a v < c' a v → u ≤ v := by
    simpa using exists_min_image _ id (filter_nonempty_iff.2 h_left)
  have h_ord : ∀ v ∈ S.jumpSet (i.stepBack a), v < u → c a u < c a v := fun v hv hvu ↦
    calc c a u < c' a u := hu_lt
      _ ≤ c' a v := h_anti hv hu hvu.le
      _ ≤ c a v := not_lt.1 fun hv_lt ↦ (h_min v hv hv_lt).not_gt hvu
  have h_free_raised : ∀ v : ℤ, ∀ n ∈ Ioo (raiseOrder c a u 0 v)
      (raiseOrder c a u 0 v + p ^ a), ¬(p : ℤ) ∣ n := by
    obtain rfl | ha := eq_or_ne a 0
    · simp only [mem_Ioo, pow_zero]; omega
    · simpa [raiseOrder, ha.symm] using h_free
  have h_le_raised (l : ℕ) (v : ℤ) : c l v ≤ raiseOrder c a u l v := by rw [raiseOrder]; omega
  have h_mem : ⟨u, c a u⟩ ∈ (S.jumpSet (i.stepBack a)).sigma fun v ↦ Ico (c a v) (c' a v) :=
    mem_sigma.2 ⟨hu, left_mem_Ico.2 hu_lt⟩
  rw [← add_sum_erase _ _ h_mem]
  -- The raised depth still satisfies the hypotheses, and has one step less.
  exact relLength_trans (relLength_deepConstants_raiseOrder_le hk h_free hc_ge h_ord)
    (ih _ h_mem h_free_raised (fun l v hv ↦ (hc_ge l v hv).trans (h_le_raised l v))
      (fun l hl v hv ↦ (hc'_le l hl v hv).trans (h_le_raised l v))
      (sigma_Ico_raiseOrder _ a u (c' a)))

/-- Raising the depth at one level `a` costs bounded length. Let `S` be a side on an unramified
chart `k`, `i` a letter, and `S.deepConstants i 0 c` the constants at `i` below elements of the
extension without pole and of depth `c`. Let `n j` and `r j` bound the residue degree `k.f` times
the numbers of jumps at `j` in `[-η, η]` and of all jumps, counted with multiplicity. Suppose no
multiple of `p` lies strictly between `c 0 v` and `c 0 v + p ^ a`, that `c l u ≥ -u` on the jumps at
`i.stepBack l`, and that `c' ≤ c` there for `l ≠ a`. If `c' a` is antitone on the jumps at
`i.stepBack a`, and the costs `k.cost a y = v_p(y) + 3 a` of the steps `c a u ≤ y < c' a u` add up
to at most `costAll` (plus `costLow` when `|u| ≤ η`), then the quotient of the constants of depth
`c` by those of depth `c'` has length at most
`costAll * r (i.stepBack a) + costLow * n (i.stepBack a)`. -/
lemma relLength_deepConstants_le (c' : ℕ → ℤ → ℤ) (hk : k.IsUnramified) {η : ℕ} {n r : Letter → ℕ}
    (hn : ∀ j : Letter, ∑ u ∈ Icc (-η : ℤ) η, k.f * S.jumpMultiplicity j u ≤ n j)
    (hr : ∀ j : Letter, ∑ u ∈ S.jumpSet j, k.f * S.jumpMultiplicity j u ≤ r j)
    (a costAll costLow : ℕ) (h_free : ∀ v : ℤ, ∀ y ∈ Ioo (c 0 v) (c 0 v + p ^ a), ¬(p : ℤ) ∣ y)
    (hc_ge : ∀ l : ℕ, ∀ u ∈ S.jumpSet (i.stepBack l), -u ≤ c l u)
    (hc'_le : ∀ l : ℕ, l ≠ a → ∀ u ∈ S.jumpSet (i.stepBack l), c' l u ≤ c l u)
    (h_anti : AntitoneOn (c' a) (S.jumpSet (i.stepBack a)))
    (h_cost : ∀ u ∈ S.jumpSet (i.stepBack a),
      ∑ y ∈ Ico (c a u) (c' a u), k.cost a y ≤
        costAll + if u ∈ Icc (-η : ℤ) η then costLow else 0) :
    relLength (S.deepConstants i 0 c) (S.deepConstants i 0 c') ≤
      (costAll * r (i.stepBack a) + costLow * n (i.stepBack a) : ℕ) := by
  -- Bound the sum over the steps line by line.
  set i' : Letter := i.stepBack a
  grw [relLength_deepConstants_le_sum_cost hk h_free hc_ge hc'_le h_anti, Nat.cast_le, sum_sigma]
  calc _ ≤ ∑ u ∈ S.jumpSet i',
          (costAll + if u ∈ Icc (-η : ℤ) η then costLow else 0) * (k.f * S.jumpMultiplicity i' u) :=
        sum_le_sum fun u hu ↦ by grw [← h_cost u hu, sum_mul]
    _ = costAll * ∑ u ∈ S.jumpSet i', k.f * S.jumpMultiplicity i' u +
          costLow * ∑ u ∈ S.jumpSet i' ∩ Icc (-η : ℤ) η, k.f * S.jumpMultiplicity i' u := by
        rw [mul_sum, mul_sum, ← sum_ite_mem, ← sum_add_distrib]
        simp only [add_mul, ite_mul, zero_mul]
    _ ≤ costAll * r i' + costLow * n i' := by grw [hr, inter_subset_right, hn]

/-- Bundled hypotheses for the few-low-jumps length and cup-orthogonality bounds on a side `S`
over an unramified Kummer chart `k` with `p ≥ 5`. -/
structure FewLowJumpsData (S : k.PairingSide O) where
  /-- The chart `k` is unramified. -/
  hk : k.IsUnramified
  /-- The prime `p` is at least `5`. -/
  hp : 5 ≤ p
  /-- The pole/cokernel parameter `a`. -/
  a : ℕ
  /-- The radius `η` of the low window `[-η, η]`. -/
  η : ℕ
  /-- The width `W` of the far windows. -/
  W : ℕ
  /-- The start `b j` of the far window at each letter `j`. -/
  b : k.Letter → ℕ
  /-- The sign `ε j` of the far window of `S` at each letter `j`. -/
  ε : k.Letter → ℤˣ
  /-- Upper bound `b j + W + η ≤ (p - 3) a` at each letter. -/
  hb_le : ∀ j : k.Letter, b j + W + η ≤ (p - 3) * a
  /-- Separation `6 (a + η + W) < b j` at each letter. -/
  hb_gt : ∀ j : k.Letter, 6 * (a + η + W) < b j
  /-- No nonzero multiple of `p` within `6 (a + η + W)` of `0` or `± b j`. -/
  hb_gap : ∀ j : k.Letter, NoMultipleNear p (6 * (a + η + W)) (b j)
  /-- The jumps of `S` fit the windows `[-η, η] ∪ ε j • [b j, b j + W]`. -/
  h_window : ∀ j : k.Letter, FitsWindows η (ε j) (b j) W (S.jumpSet j)
  /-- Upper bound `n j` on `k.f` times the low jump multiplicities at each letter `j`. -/
  n : k.Letter → ℕ
  /-- Upper bound `r j` on `k.f` times all jump multiplicities at each letter `j`. -/
  r : k.Letter → ℕ
  /-- `n j` bounds `k.f` times the jumps of `S` in `[-η, η]` at `j`. -/
  hn : ∀ j : k.Letter, ∑ u ∈ Icc (-η : ℤ) η, k.f * S.jumpMultiplicity j u ≤ n j
  /-- `r j` bounds `k.f` times all jumps of `S` at `j`. -/
  hr : ∀ j : k.Letter, ∑ u ∈ S.jumpSet j, k.f * S.jumpMultiplicity j u ≤ r j

/-- Package `S` with an opposite-window paired side `T` into `OppositeWindowSides`. -/
def FewLowJumpsData.toOpposite (D : FewLowJumpsData S) {T : k.PairingSide O} (P : T.SidePairing S)
    (hT : ∀ j : k.Letter, FitsWindows D.η (-D.ε j) (D.b j) D.W (T.jumpSet j)) :
    OppositeWindowSides P :=
  ⟨D.η, D.W, D.b, D.ε, hT, D.h_window⟩

/-- Let the chart `k` be unramified, `p ≥ 5`, and let `p` divide no nonzero integer within
`6 (a + η + W)` of `0` or `± b j`, for every letter `j`. Let `X` be a side over the coefficients
`O`, all of whose jumps, the elements of its sets `X.jumpSet j`, are at most `(p - 3) (κ + s)`, so
that `p ^ κ * E ^ s` kills its cokernels (`E = z + p`). Let the integers in `[-s - u, t - u)` lie
within `6 (a + η + W)` of `0` or `± b i` for the jumps `u` at the letter `i`. Then `X` has an
element of the extension over `p ^ κ • x` at `i` of depth `raisedOrdersAtZero t`, that is, its
differences with its translates by the group of the chart have order `t - u` at the level `0` and
`-u` above on the line of the jump `u`. Its own orders are `t - u` at the level `0` if `u < -s`,
else `min (t - u) 0`, and `-u` above. -/
lemma FewLowJumpsData.pointsOver_raisedOrdersAtZero_nonempty (D : FewLowJumpsData S)
    {X : PairingSide O} (x : X.paramLattice) (i : Letter) (κ s : ℕ) (t : ℤ)
    (h_top : ∀ j : Letter, ∀ u ∈ X.jumpSet j, u ≤ ((p - 3) * (κ + s) : ℕ))
    (h_near : ∀ u ∈ X.jumpSet i, ∀ y : ℤ, -s - u ≤ y → y < t - u →
      y ∈ twoWindows (6 * (D.a + D.η + D.W)) (D.b i) ∪
        twoWindows (6 * (D.a + D.η + D.W)) (-D.b i)) :
    (X.pointsOver x i κ (improvedOrders (raisedOrdersAtZero (-s)) (raisedOrdersAtZero t))
      (raisedOrdersAtZero t)).Nonempty := by
  refine pointsOver_nonempty_of_near_steps D.hk (D.hb_gap i)
    (pointsOver_nonempty_of_killsCokernel (killsCokernel_of_isUnramified κ s h_top D.hk D.hp) x)
    ?_ fun _ _ _ ↦ le_rfl
  rintro (_ | l) u hu y hy_ge hy_lt
  · exact ⟨rfl, h_near u hu y hy_ge hy_lt⟩
  · exact absurd hy_lt (not_lt.2 hy_ge)

/-- Let `X` be a side on an unramified chart `k` and `p ≥ 5`; at every letter `j` let
`b j + W + η ≤ (p - 3) a`, let `p` divide no nonzero integer within `6 (a + η + W)` of `0` or
`± b j`, and let the jumps lie in `[-η, η]` or in `σ j • [b j, b j + W]`. Then there is an element
of the extension over `p ^ s • d` at the letter `i` of depth `raisedOrdersAtZero (2a + η)`: its
differences with its translates by the group of the chart have order `2a + η - u` at the level `0`
and `-u` above on the line of the jump `u`. With `a - s` taken in `ℕ`, its own orders are
`2a + η - u` at the level `0` if `u < -(a - s)`, else `min (2a + η - u) 0`, and `-u` above. -/
lemma FewLowJumpsData.pointsOver_raisedOrdersAtZero_nonempty_of_fitsWindows (D : FewLowJumpsData S)
    {X : k.PairingSide O} {σ : Letter → ℤˣ}
    (h_window : ∀ j : Letter, FitsWindows D.η (σ j) (D.b j) D.W (X.jumpSet j)) (s : ℕ)
    (d : X.paramLattice) :
    (X.pointsOver d i s (improvedOrders (raisedOrdersAtZero (-(D.a - s : ℕ)))
      (raisedOrdersAtZero (2 * D.a + D.η))) (raisedOrdersAtZero (2 * D.a + D.η))).Nonempty := by
  refine D.pointsOver_raisedOrdersAtZero_nonempty d i s (D.a - s) _ (fun j u hu ↦ ?_)
    fun u hu y hy_ge hy_lt ↦ ?_
  · grw [← le_add_tsub]
    have := D.hb_le j
    grind [low_or_far_of_fitsWindows (h_window j) hu]
  · grind [low_or_far_of_fitsWindows (h_window i) hu, mem_twoWindows_union_iff]

/-- Let `S` be a side on an unramified chart `k` and `p ≥ 5`; at every letter `j` let
`b j + W + η ≤ (p - 3) a`, let `p` divide no nonzero integer within
`6 (a + η + W)` of `0` or `± b j`, and let the jumps of `S` lie in `[-η, η]` or in
`ε j • [b j, b j + W]`. Write `raisedOrdersAtZero t` for the orders that on the line of a jump `u`
are `t - u` at the level `0` and `-u` above. With `a - s` taken in `ℕ`, a point with orders
`raisedOrdersAtZero (-(a - s))` and depth `raisedOrdersAtZero (2a + η)` has the improved orders:
`2a + η - u` at the level `0` if `u < -(a - s)`, else `min (2a + η - u) 0`, and `-u` above. If
`raisedOrdersAtZero t` is at most these on the jumps, then `p ^ s` times the letter-`i` part
`S.constantAt i d` of `1 ⊗ d` lies in `S.deepConstants i t`: below an element of the extension with
orders `raisedOrdersAtZero t` and depth `raisedOrdersAtZero (2a + η)`. -/
lemma FewLowJumpsData.pow_smul_constantAt_mem_deepConstants (D : FewLowJumpsData S) (s : ℕ)
    (d : S.paramLattice) {t : ℤ}
    (ht : ∀ l : ℕ, ∀ u ∈ S.jumpSet (i.stepBack l), raisedOrdersAtZero t l u ≤
      improvedOrders (raisedOrdersAtZero (-(D.a - s : ℕ)))
        (raisedOrdersAtZero (2 * D.a + D.η)) l u) :
    p ^ s • S.constantAt i d ∈ S.deepConstants i t (raisedOrdersAtZero (2 * D.a + D.η)) := by
  -- `p ^ s E ^ (a - s)` kills the cokernel, which gives a deep point over `p ^ s • d`.
  obtain ⟨x, hx_mem, hx_const, hx_exp, hx_inv⟩ :=
    D.pointsOver_raisedOrdersAtZero_nonempty_of_fitsWindows (i := i) D.h_window s d
  exact ⟨⟨x, hx_mem⟩, ⟨mem_withOrders_of_le hx_exp ht,
    mem_deepElements_iff_mem_range_and_invariantsMod.2 ⟨by simp [hx_const, nsmul_mem], hx_inv⟩⟩,
    by simp [hx_const]⟩

/-- Lowering the pole order by one. Let `S` be a side on an unramified chart `k`, `i` a letter,
`t < 0` and `t < s`. `S.deepConstants i t o` consists of the constants at `i` below elements of the
extension with orders `raisedOrdersAtZero t` and depth `o`. Suppose that `p ^ a` times every
constant at `i` lies in this module for `t + 1` and the depth `raisedOrdersAtZero s`. Then its
quotient from `t` to `t + 1` has length (`relLength`) at most `a` times the residue degree `k.f`
times the multiplicity of the jump `t` at `i`. -/
lemma relLength_deepConstants_add_one_le (hk : k.IsUnramified) {a : ℕ} {s t : ℤ} (ht_neg : t < 0)
    (hts : t < s)
    (h_kill : ∀ d : S.paramLattice, p ^ a • S.constantAt i d ∈ S.deepConstants i (t + 1)
      (raisedOrdersAtZero s)) :
    relLength (S.deepConstants i t (raisedOrdersAtZero s))
      (S.deepConstants i (t + 1) (raisedOrdersAtZero s)) ≤
      (a * (k.f * S.jumpMultiplicity i t) : ℕ) := by
  rw [deepConstants, ← relLength_comap]
  refine relLength_le_of_relations a (fun _ ⟨_, ⟨d, hd⟩, _⟩ ↦ by simpa [hd] using h_kill d)
    fun x hx ↦ ?_
  obtain ⟨hx_exp, hx_deep⟩ := forall_and.1 fun j ↦ (hx j).1
  -- As `t ≠ 0`, the extension has no more jumps `t` than the sublattice.
  have h_jumps : S.extensionLattice.jumpMultiplicity (i.stepBack 0) t ≤ S.jumpMultiplicity i t :=
    sum_le_sum fun _ _ ↦ jump_extensionRep_le _ ht_neg.ne
  obtain ⟨β, j, hβ_one, h_comb⟩ := exists_sum_smul_mem_locKisinPart_sup (raisedOrdersAtZero t) hk 0
    i h_jumps (by simp [raisedOrdersAtZero]) x hx_exp
  have h_raised : ∑ j, β j • x j ∈
      locKisinPart (S.extensionLattice.withOrders i (raiseOrder (raisedOrdersAtZero t) 0 t)) := by
    rwa [sup_of_le_right fun _ hy ↦ mem_withOrders_of_le hy fun l v _ ↦ by
      simp only [raiseOrder, raiseOrdersAt]; omega] at h_comb
  have h_deep : ∑ j, β j • x j ∈ S.deepElements i (raisedOrdersAtZero s) :=
    sum_smul_mem _ β fun j _ ↦ hx_deep j
  -- A deep point with one more exponent on the line `t` has a pole of order at most `-(t + 1)`.
  exact ⟨β, j, hβ_one, mem_map_of_mem ⟨mem_withOrders_of_le
    (mem_withOrders_improvedOrders h_raised h_deep.2) fun l v _ ↦ by
      simp only [raisedOrdersAtZero, raiseOrder, improvedOrders]; omega, h_deep⟩⟩

/-- Removing the pole. Let `S` be a side on an unramified chart `k` and `p ≥ 5`; at every letter `j`
let `b j + W + η ≤ (p - 3) a` and `6 (a + η + W) < b j`, let `p` divide no nonzero integer within
`6 (a + η + W)` of `0` or `± b j`, let the jumps of `S` lie in `[-η, η]` or in
`ε j • [b j, b j + W]`, and let `n j` bound the residue degree `k.f` times the number of jumps in
`[-η, η]`, counted with multiplicity. The constants at the letter `i` are the letter-`i` parts
`S.constantAt i d` of `1 ⊗ d`. Their quotient by those that lie below elements of the extension
without pole (orders `-u` on each jump line `u`) and of depth `raisedOrdersAtZero (2a + η)` has
length at most `a * n i`. -/
lemma FewLowJumpsData.relLength_constantAt_range_deepConstants_le (D : FewLowJumpsData S)
    (i : Letter) :
    relLength (S.constantAt i).range (S.deepConstants i 0 (raisedOrdersAtZero (2 * D.a + D.η))) ≤
      (D.a * D.n i : ℕ) := by
  -- Every constant has a deep point with a pole of order at most `η`. Lower the order stepwise:
  -- the step from `t` to `t + 1` loses at most `a * k.f` times the number of jumps `t`.
  have h_start : relLength (S.constantAt i).range
      (S.deepConstants i (-D.η) (raisedOrdersAtZero (2 * D.a + D.η))) = 0 := by
    rw [relLength_eq_zero]
    rintro _ ⟨d, rfl⟩
    rw [← one_smul ℕ (S.constantAt i d), ← pow_zero p]
    refine D.pow_smul_constantAt_mem_deepConstants 0 d fun l u hu ↦ ?_
    -- No jump lies in `[-a, -η)`.
    have := D.hb_gt (i.stepBack l)
    simp only [raisedOrdersAtZero, improvedOrders]
    obtain _ | _ | _ := low_or_far_of_fitsWindows (D.h_window _) hu <;> omega
  have h_kill (t : ℤ) (ht : t ≤ 0) (d : S.paramLattice) :
      p ^ D.a • S.constantAt i d ∈ S.deepConstants i t (raisedOrdersAtZero (2 * D.a + D.η)) :=
    D.pow_smul_constantAt_mem_deepConstants D.a d fun _ _ _ ↦ by
      simp only [raisedOrdersAtZero, improvedOrders]; omega
  have h_pole : ∀ t : ℤ, -D.η ≤ t → t ≤ 0 →
      relLength (S.constantAt i).range (S.deepConstants i t (raisedOrdersAtZero (2 * D.a + D.η))) ≤
        (D.a * ∑ u ∈ Ico (-D.η : ℤ) t, k.f * S.jumpMultiplicity i u : ℕ) := by
    refine Int.leInduction (fun _ ↦ h_start.trans_le bot_le) fun t ht ih ht_le ↦ ?_
    rw [← sum_Ico_add_eq_sum_Ico_add_one ht, mul_add]
    exact relLength_trans (ih (by lia))
      (relLength_deepConstants_add_one_le D.hk (by lia) (by lia) (h_kill (t + 1) ht_le))
  grw [h_pole 0 (by lia) le_rfl, Ico_subset_Icc_self, D.η.cast_nonneg, D.hn]

/-- In the unramified chart the steps `0, …, N` at the level `0` together cost `v_p(N!)`. Here the
cost of a step `n` at the level `0` is `v_p(n) + k.differentBound`. -/
lemma sum_cost_zero_eq_padicValNat_factorial (hk : k.IsUnramified) (N : ℕ) :
    ∑ m ∈ Ico (0 : ℤ) (N + 1), k.cost 0 m = padicValNat p N.factorial := by
  simp only [cost, hk.2, mul_zero, add_zero]
  induction N with
  | zero => simp [show Ico (0 : ℤ) 1 = {0} from rfl, Nat.padicValNat_def]
  | succ N ih =>
    rw [Nat.cast_succ, ← insert_Ico_right_eq_Ico_add_one (by positivity), sum_insert (by simp), ih,
      ← Nat.cast_succ, padicValInt.of_nat, Nat.factorial_succ, Nat.padicValNat_def,
      Nat.padicValNat_def, Nat.multiplicity_mul N.succ_ne_zero N.factorial_ne_zero]

/-- In the unramified chart the steps `0, …, N` at the level `0` together cost at most `m` if
`N ≤ (p - 1) m`, by Legendre's formula. -/
lemma sum_cost_zero_le (hk : k.IsUnramified) {N m : ℕ} (hN : N ≤ (p - 1) * m) :
    ∑ y ∈ Ico (0 : ℤ) (N + 1), k.cost 0 y ≤ m := by
  rw [sum_cost_zero_eq_padicValNat_factorial hk]
  refine le_of_mul_le_mul_left ?_ (tsub_pos_of_lt (Fact.out : p.Prime).one_lt)
  grw [Nat.padicValNat_def, Nat.Prime.sub_one_mul_multiplicity_factorial Fact.out, Nat.sub_le, hN]

/-- Let the Kummer chart `k` of the prime `p ≥ 5` be unramified, so that the cost `k.cost 0 y` of
the step `y` at the level `0` is `v_p(y)`, with `v_p(0) = 0`. Let `β + W + η ≤ (p - 3) a`, let `p`
divide no nonzero integer within `6 (a + η + W)` of `0` or `± β`, and let `t` be a multiple
of `p` below `β + W + a + η + p`. For `u` in `[-η, η]` or in `-[β, β + W]`, the steps `y`
with `2a + η - u ≤ y < t` cost at most `a + 1` together, and nothing if `u` is not in
`[-η, η]`. -/
lemma sum_cost_zero_Ico_multiple_le (hk : k.IsUnramified) (hp : 5 ≤ p)
    {a η W β : ℕ} {u t : ℤ}
    (h_top : β + W + η ≤ (p - 3) * a) (h_gap : NoMultipleNear p (6 * (a + η + W)) (β : ℤ))
    (hu : (-η ≤ u ∧ u ≤ η) ∨ (β ≤ -u ∧ -u ≤ β + W)) (ht_dvd : (p : ℤ) ∣ t)
    (ht_lt : t < β + W + a + η + p) :
    ∑ y ∈ Ico (2 * a + η - u) t, k.cost 0 y ≤ if u ∈ Icc (-η : ℤ) η then a + 1 else 0 := by
  split_ifs with h_low
  · -- the steps lie in `[0, t]`, and `t ≤ (p - 1) (a + 1)`
    have h_split : (p - 1) * (a + 1) = (p - 3) * a + 2 * a + (p - 1) := by
      rw [show p - 1 = p - 3 + 2 by omega]; ring
    exact (sum_le_sum_of_subset (Ico_subset_Ico (by omega) (by omega))).trans
      (sum_cost_zero_le hk (by omega : t.toNat ≤ (p - 1) * (a + 1)))
  · -- a step `y < t` divisible by `p` has `y ≤ t - p`, so it is near `β` and hence is `0`
    refine sum_nonpos fun y hy ↦ cost_le_of_isUnramified hk fun h_dvd ↦
      h_gap.eq_zero_of_dvd ?_ h_dvd
    have h_dist : (p : ℤ) ≤ t - y := le_of_dvd (sub_pos.2 (mem_Ico.1 hy).2) (ht_dvd.sub h_dvd)
    grind [mem_twoWindows_union_iff]

/-- Let the Kummer chart `k` be unramified, so that the cost `k.cost 1 y` of the step `y` at the
level `1` is `v_p(y) + 3`. Let `6 (a + η + W) < β`, let `p` divide no nonzero integer within
`6 (a + η + W)` of `0` or `± β`, and let `u` lie in `[-η, η]` or in `σ • [β, β + W]`. The depth
`negativeWindowDepth a η W β' 1 u` is `W + 1 - u`, plus `2a` if `|u| ≤ η`; the window start `β'`
enters this function only at the level `0`, so it is arbitrary here. The steps `y ≥ -u` below this
depth cost at most `3 (W + 1)`, plus `6a` if `|u| ≤ η`. -/
lemma sum_cost_one_Ico_negativeWindowDepth_le (hk : k.IsUnramified)
    {a η W β : ℕ} (β' : ℕ) {σ : ℤˣ} {U : Finset ℤ} {u : ℤ} (h_far : 6 * (a + η + W) < β)
    (h_gap : NoMultipleNear p (6 * (a + η + W)) (β : ℤ)) (h_window : FitsWindows η σ β W U)
    (hu : u ∈ U) :
    ∑ y ∈ Ico (-u) (negativeWindowDepth a η W β' 1 u), k.cost 1 y ≤
      3 * (W + 1) + if u ∈ Icc (-η : ℤ) η then 6 * a else 0 := by
  have h_depth :
      negativeWindowDepth a η W β' 1 u = W + 1 - u + if -η ≤ u ∧ u ≤ η then 2 * a else 0 := by
    simp [negativeWindowDepth, abs_le]
  -- there are at most `W + 1 + 2 a` steps, each prime to `p` or `0`, hence of cost at most `3`
  have h_step : ∀ y ∈ Ico (-u) (negativeWindowDepth a η W β' 1 u), k.cost 1 y ≤ 3 * 1 := fun y hy ↦
    cost_le_of_isUnramified hk
      (h_gap.eq_zero_of_dvd (by grind [low_or_far_of_fitsWindows h_window hu]))
  grw [sum_le_card_nsmul _ _ _ h_step, h_depth, Int.card_Ico, smul_eq_mul]
  simp only [mem_Icc]
  split_ifs <;> omega

/-- Let `S` be a side on an unramified Kummer chart `k` and `p ≥ 5`. At every letter `j` let
`b j + W + η ≤ (p - 3) a` and `6 (a + η + W) < b j`, let `p` divide no nonzero integer within
`6 (a + η + W)` of `0` or `± b j`, let the jumps of `S` lie in `[-η, η]` or in
`ε j • [b j, b j + W]`, and let `n j` and `r j` bound the residue degree `k.f` times the numbers of
low jumps and of all jumps, counted with multiplicity. Let `ε i = -1` and let `m = i.stepBack 1` be
the previous letter. `S.deepConstants i 0 o` consists of the constants at `i` below elements of the
extension without pole (orders `-u` on the line of each jump `u`) and of depth `o`. The depth
`raisedOrdersAtZero (2a + η)` is `2a + η - u` at the level `0` and `-u` above; the depth
`negativeWindowDepth a η W (b i)` is `b i + W + a + η` at the level `0`, `W + 1 - u` (plus `2a` if
`|u| ≤ η`) at the level `1`, and `-u` above. The quotient of the constants for the first depth by
those for the second has length at most `(a + 1) n i + 3 (W + 1) r m + 6a n m`. -/
lemma FewLowJumpsData.relLength_deepConstants_negativeWindowDepth_le (D : FewLowJumpsData S)
    (i : k.Letter) (hε : D.ε i = -1) :
    relLength (S.deepConstants i 0 (raisedOrdersAtZero (2 * D.a + D.η)))
        (S.deepConstants i 0 (negativeWindowDepth D.a D.η D.W (D.b i))) ≤
      ↑((D.a + 1) * D.n i +
        (3 * (D.W + 1) * D.r (i.stepBack 1) + 6 * D.a * D.n (i.stepBack 1))) := by
  -- Use `relLength_deepConstants_le` twice: change the depth at the level `0` to a constant
  -- multiple of `p` (where it falls, nothing is paid), then raise the depth at the level `1`.
  have hp_pos : (0 : ℤ) < p := natCast_pos.2 p.pos_of_neZero
  have h_win : ∀ u ∈ S.jumpSet i, (-D.η ≤ u ∧ u ≤ D.η) ∨ (D.b i ≤ -u ∧ -u ≤ D.b i + D.W) := by
    simpa [FitsWindows, hε] using D.h_window i
  -- `q * p` is the least multiple of `p` that is at least `b i + W + a + η`
  obtain ⟨q, hq_ge, hq_lt⟩ :
      ∃ q : ℤ, D.b i + D.W + D.a + D.η ≤ q * p ∧ q * p < D.b i + D.W + D.a + D.η + p := by
    simpa using (existsUnique_add_zsmul_mem_Ico hp_pos 0 (D.b i + D.W + D.a + D.η)).exists
  let d (l : ℕ) (u : ℤ) : ℤ := if l = 0 then q * p else -u
  -- Level `0`: far lines are free, and a low line costs at most `a + 1`.
  have h_level_zero : relLength (S.deepConstants i 0 (raisedOrdersAtZero (2 * D.a + D.η)))
      (S.deepConstants i 0 d) ≤ ↑(0 * D.r i + (D.a + 1) * D.n i) := by
    refine relLength_deepConstants_le d D.hk D.hn D.hr 0 0 (D.a + 1)
      (fun _ _ hy ↦ by rw [mem_Ioo, pow_zero] at hy; omega)
      (fun _ _ _ ↦ by simp only [raisedOrdersAtZero]; omega)
      (fun _ _ _ _ ↦ by simp only [d, raisedOrdersAtZero]; omega) antitoneOn_const fun u hu ↦ by
        simpa [d, raisedOrdersAtZero] using sum_cost_zero_Ico_multiple_le D.hk D.hp (D.hb_le i)
          (D.hb_gap i) (h_win u hu) (dvd_mul_left _ q) hq_lt
  -- Level `1`: a line has `W + 1` steps, `2 * a` more if it is low; each costs at most `3`.
  set m : Letter := i.stepBack 1
  have h_level_one : relLength (S.deepConstants i 0 d)
      (S.deepConstants i 0 (negativeWindowDepth D.a D.η D.W (D.b i))) ≤
        ↑(3 * (D.W + 1) * D.r m + 6 * D.a * D.n m) := by
    refine relLength_deepConstants_le _ D.hk D.hn D.hr 1 _ _
      -- no multiple of `p` lies strictly between `q * p` and `q * p + p`
      (fun _ y hy ↦ (not_dvd_iff_lt_mul_succ y hp_pos).2
        ⟨q, by simpa [d, mul_comm, mul_add] using hy⟩)
      -- the jumps `u` at `i` have `-u ≤ b i + W + η ≤ q * p`
      (by rintro (_ | l) u hu
          · have := h_win u hu; simp only [d, ite_true]; omega
          · simp [d])
      -- at the level `0` the depth only falls, from `q * p` to `b i + W + a + η`
      (by rintro (_ | _ | l) hl u -
          · simpa only [d, negativeWindowDepth, ite_true] using hq_ge
          · exact absurd rfl hl
          · simp [d, negativeWindowDepth])
      (fun u hu v hv h_le ↦ by
        have := D.hb_gt m
        have := low_or_far_of_fitsWindows (D.h_window m) hu
        have := low_or_far_of_fitsWindows (D.h_window m) hv
        simp only [negativeWindowDepth, one_ne_zero, ite_false, ite_true, abs_le]
        split_ifs <;> omega)
      fun u hu ↦ by
        simpa [d] using sum_cost_one_Ico_negativeWindowDepth_le D.hk (D.b i) (D.hb_gt m)
          (D.hb_gap m) (D.h_window m) hu
  simpa using relLength_trans h_level_zero h_level_one

/-- Let `S` be a side on an unramified Kummer chart `k` and `p ≥ 5`. At every letter `j` let
`b j + W + η ≤ (p - 3) a` and `6 (a + η + W) < b j`, let `p` divide no nonzero integer within
`6 (a + η + W)` of `0` or `± b j`, let the jumps of `S` lie in `[-η, η]` or in
`ε j • [b j, b j + W]`, and let `n j` and `r j` bound the residue degree `k.f` times the numbers of
low jumps and of all jumps, counted with multiplicity. The constants at the letter `i` are the
letter-`i` parts `S.constantAt i d` of `1 ⊗ d` for `d` in `S.paramLattice`. Their quotient by those
that lie below an element of the extension without pole whose differences with its translates by the
group of the chart have orders `fewLowJumpsDepth a η W (b i) (ε i)` has length at most
`(2a + 1) n i + 3 (W + 1) r m + 6a n m`, where `m = i.stepBack 1` is the previous letter. -/
lemma FewLowJumpsData.relLength_constantAt_deepConstants_le (D : FewLowJumpsData S) (i : k.Letter) :
    relLength (S.constantAt i).range
        (S.deepConstants i 0 (fewLowJumpsDepth D.a D.η D.W (D.b i) (D.ε i))) ≤
      ↑((2 * D.a + 1) * D.n i + (3 * (D.W + 1) * D.r (i.stepBack 1) +
        6 * D.a * D.n (i.stepBack 1))) := by
  have h_pole := D.relLength_constantAt_range_deepConstants_le i
  rw [fewLowJumpsDepth]
  split_ifs with hε
  · exact h_pole.trans (mod_cast by lia)
  · exact (relLength_trans h_pole (D.relLength_deepConstants_negativeWindowDepth_le i
      ((units_eq_one_or _).resolve_left hε))).trans (mod_cast by lia)

/-- Let `b j + W + η ≤ (p - 3) a` and `6 (a + η + W) < b j` at every letter `j`. If the jumps of the
paired sides `T` and `S` lie in `[-η, η]` or in far windows `∓ε j [b j, b j + W]` of opposite signs,
then the jumps of the Tate dual side are at most `(p - 3) a`. -/
lemma FewLowJumpsData.tateDualSide_jump_le (D : FewLowJumpsData S) {T : PairingSide O}
    (P : SidePairing T S)
    (hT_window : ∀ j : Letter, FitsWindows D.η (-D.ε j) (D.b j) D.W (T.jumpSet j)) (j : Letter)
    (u : ℤ) (hu : u ∈ P.tateDualSide.jumpSet j) : u ≤ ((p - 3) * D.a : ℕ) := by
  have h := (D.toOpposite P hT_window).tateDualSide_jump_near hu
  simp only [FewLowJumpsData.toOpposite, abs_eq_max_neg] at h
  have := D.hb_le j; have := D.hb_gt j; omega

/-- The inequality for a safe move at the level `1`. Let `6 (a + η + W) < β`, let the jump `u` of
the moving side lie in `[-η, η]` or in `-σ • [β, β + W]`, and the jump `v` of the resting side in
`[-η, η]` or in `σ • [β, β + W]`; then `-u - v - 1` is the jump of the Tate dual side that pairs
with them. Write `e t w` for `improvedOrders (raisedOrdersAtZero (-a)) (raisedOrdersAtZero t) 0 w`,
which is `t - w` if `w < -a` and `min (t - w) 0` otherwise. The sum of the orders `e a (-u - v - 1)`
of the dual point and `min (-u) (e (2a + η) u)` of the move and of the depth
`negativeWindowDepth a η W β' 1 v` of the resting point is positive. -/
lemma improvedOrders_add_negativeWindowDepth_one_pos {a η W : ℕ} {σ : ℤˣ} {β β' : ℕ}
    {U V : Finset ℤ} {u v : ℤ} (h_far : 6 * (a + η + W) < β)
    (hU_window : FitsWindows η (-σ) β W U) (hu : u ∈ U)
    (hV_window : FitsWindows η σ β W V) (hv : v ∈ V) :
    0 < improvedOrders (raisedOrdersAtZero (-a)) (raisedOrdersAtZero a) 0 (-u - v - 1) +
      min (-u) (improvedOrders (raisedOrdersAtZero (-a)) (raisedOrdersAtZero (2 * a + η)) 0 u) +
      negativeWindowDepth a η W β' 1 v := by
  simp only [improvedOrders, raisedOrdersAtZero, negativeWindowDepth, one_ne_zero, ite_false,
    ite_true, min_def, abs_le]
  have := hU_window u hu; have := hV_window v hv
  have : ((-σ : ℤˣ) : ℤ) = -(σ : ℤ) := Units.val_neg σ
  split_ifs <;> omega

/-- Let the chart `k` be unramified, `p ≥ 5` and `η ≥ 1`; at every letter `j` let
`b j + W + η ≤ (p - 3) a` and `6 (a + η + W) < b j`, let `p` divide no nonzero integer within
`6 (a + η + W)` of `0` or `± b j`, and let the jumps of the paired sides `S` and `T` lie in
`[-η, η]` or in the opposite far windows `± ε j • [b j, b j + W]`. Let `x₀` and `x` be points of `T`
over `c` at the letter before `i` and at `i`, of depth `raisedOrdersAtZero (2a + η)`. At the level
`0` their own orders are `2a + η - u` if `u < -a`, else `min (2a + η - u) 0`, and `-u` above. Let
`x'` be a point of `S` over `d` at `i` with any orders `o'` and depth
`negativeWindowDepth a η W (b i)`: `b i + W + a + η` at the level `0`, `W + 1 - u` (plus `2a` if
`|u| ≤ η`) at the level `1`, and `-u` above. Then the move by `φ x₀ - x`, with `φ` the Frobenius, is
safe with `x'` at rest: for every `g` in the group `k.galMonoid` of the chart, `P` pairs the
components in the lattices of `T` and `S` of `φ x₀ - x` and `g • x' - x'` into the image of
`W(𝔪^♭)`, the Witt vectors of the maximal ideal of the tilt. -/
lemma FewLowJumpsData.isSafeMoveFst_of_negativeWindowDepth (D : FewLowJumpsData S)
    {T : k.PairingSide O} (P : T.SidePairing S)
    (hT_window : ∀ j : k.Letter, FitsWindows D.η (-D.ε j) (D.b j) D.W (T.jumpSet j))
    {c : T.paramLattice} {d : S.paramLattice} {o' : ℕ → ℤ → ℤ}
    {x₀ x : T.extensionLattice.Ambient} {x' : S.extensionLattice.Ambient}
    (hx : x ∈ T.pointsOver c i 0
      (improvedOrders (raisedOrdersAtZero (-D.a)) (raisedOrdersAtZero (2 * D.a + D.η)))
      (raisedOrdersAtZero (2 * D.a + D.η)))
    (hx₀ : x₀ ∈ T.pointsOver c (i.stepBack 1) 0
      (improvedOrders (raisedOrdersAtZero (-D.a)) (raisedOrdersAtZero (2 * D.a + D.η)))
      (raisedOrdersAtZero (2 * D.a + D.η)))
    (hx' : x' ∈ S.pointsOver d i 0 o' (negativeWindowDepth D.a D.η D.W (D.b i))) :
    P.IsSafeMoveFst 0 (FrobGroup.φ ^ 1 • x₀ - x) x' := by
  -- Apply the rule, weight by weight, with `φ` of a point of the Tate dual side at the letter
  -- before `i` that has been deepened to `raisedOrdersAtZero a` by near steps.
  let z := improvedOrders (raisedOrdersAtZero (-D.a)) (raisedOrdersAtZero D.a)
  let o := improvedOrders (raisedOrdersAtZero (-D.a)) (raisedOrdersAtZero (2 * D.a + D.η))
  obtain ⟨_, hx''⟩ := D.pointsOver_raisedOrdersAtZero_nonempty (X := P.tateDualSide) 1
    (i.stepBack 1) 0 D.a D.a
    (by simpa only [zero_add] using D.tateDualSide_jump_le P hT_window) fun u hu y hy_ge hy_lt ↦ by
      rw [mem_twoWindows_union_iff]
      have h := (D.toOpposite P hT_window).tateDualSide_jump_near hu
      simp only [FewLowJumpsData.toOpposite, abs_eq_max_neg] at h; omega
  have h_standard (s t : ℤ) (l : ℕ) (w : ℤ) :
      improvedOrders (raisedOrdersAtZero s) (raisedOrdersAtZero t) (l + 1) w = -w := by
    simp only [improvedOrders, raisedOrdersAtZero]; omega
  refine P.isSafeMoveFst_of_orders hx''
    (fun _ _ _ _ ↦ by simp only [improvedOrders, raisedOrdersAtZero]; omega)
    (sub_mem_kerWithOrders_of_pointsOver hx (phi_pow_smul_mem_pointsOver hx₀)) hx'
    fun l u hu v hv ↦ ?_
  rcases l with _ | _ | m
  · -- At the level `0` the depth `b i + W + a + η` exceeds the pole of `x`.
    change 0 < 0 + min (o 0 u) 0 + (D.b i + D.W + D.a + D.η)
    have := D.hb_gt i
    have : 0 < D.a := Nat.pos_of_mul_pos_left (by have := D.hb_le i; omega : 0 < (p - 3) * D.a)
    simp only [o, raisedOrdersAtZero, ite_true, min_def]
    obtain _ | _ | _ := low_or_far_of_fitsWindows (hT_window i) hu <;> split_ifs <;> omega
  · change 0 < z 0 (-u - v - 1) + min (o (0 + 1) u) (o 0 u) +
      negativeWindowDepth D.a D.η D.W (D.b i) 1 v
    rw [show o (0 + 1) u = -u from h_standard _ _ 0 u]
    exact improvedOrders_add_negativeWindowDepth_one_pos (D.hb_gt _) (hT_window _) hu
      (D.h_window _) hv
  · -- At the higher levels the three orders are the standard ones.
    change 0 < z (m + 1) (-u - v - 1) + min (o (m + 2) u) (o (m + 1) u) + -v
    simp only [z, o, h_standard]; omega

/-- Let `S` be a side on an unramified chart `k` and `p ≥ 5`. At every letter `i` let
`b i + W + η ≤ (p - 3) a` and `6 (a + η + W) < b i`, let `p` divide no nonzero integer within
`6 (a + η + W)` of `0` or `± b i`, let the jumps lie in `[-η, η]` or in `ε i • [b i, b i + W]`, and
let `n i` and `r i` bound the residue degree `k.f` times the numbers of low jumps and of all jumps,
counted with multiplicity. Take the `d` in `S.paramLattice` such that at every letter `i` the
letter-`i` part `S.constantAt i d` of `1 ⊗ d` lies below an element of the extension without pole
whose differences with its translates by the group of the chart have the orders
`fewLowJumpsDepth a η W (b i) (ε i)`. They form a `ℤ_[p]`-submodule of `S.paramLattice` with
quotient of length at most `∑ i, (n i (8a + 1) + 3 r i (W + 1))`. -/
lemma FewLowJumpsData.relLength_iInf_comap_deepConstants_le (D : FewLowJumpsData S) :
    relLength (⊤ : Submodule ℤ_[p] S.paramLattice)
        (⨅ i : k.Letter, (S.deepConstants i 0 (fewLowJumpsDepth D.a D.η D.W (D.b i) (D.ε i))).comap
          (S.constantAt i)) ≤
      (∑ i : k.Letter, (D.n i * (8 * D.a + 1) + D.r i * (3 * (D.W + 1))) : ℕ) := by
  -- `i ↦ i.stepBack 1` permutes the letters
  have h_perm (f : Letter → ℕ) : ∑ i : Letter, f (i.stepBack 1) = ∑ i : Letter, f i := by
    simp [Equiv.sum_comp]
  grw [relLength_iInf_le]
  simp_rw [relLength_comap, Submodule.map_top]
  grw [sum_le_sum fun i _ ↦ D.relLength_constantAt_deepConstants_le i]
  norm_cast
  simp only [sum_add_distrib, ← mul_sum, ← sum_mul, h_perm]
  exact le_of_eq (by ring)

/-- Scaled cup coboundaries for few low jumps. Let `k` be an unramified Kummer chart with constants
`W(𝔽_{p ^ k.f})`, whose letters are the units of `𝔽_{p ^ k.f}`, and let `p ≥ 5` and `η ≥ 1`. Let
`S` be a side over the coefficients `O`: a Galois lattice `Y`, a linear map `S.cocycleMap` from a
lattice `S.paramLattice` to the crystalline cocycles of `Y`, and sets `S.jumpSet i` that contain the
Hodge–Tate jumps of `Y` at the letters `i`. Suppose that at every letter `i`
* `b i + W + η ≤ (p - 3) a` and `6 (a + η + W) < b i`;
* `p` divides no nonzero integer within `6 (a + η + W)` of `0`, `b i` or `-b i`;
* `S.jumpSet i` lies in the union of the low window `[-η, η]` and the far window
`ε i • [b i, b i + W]`;
* `n i` and `r i` bound `k.f` times the number of jumps of `Y` at `i` in `[-η, η]` and in
`S.jumpSet i`, counted with multiplicity.

Then there is a `ℤ_[p]`-submodule `V` of `S.paramLattice` such that `S.paramLattice / V` has length
at most `∑ i, (n i (8a + 1) + 3 r i (W + 1))`, and `V` cups to zero. That is, let `T` be a second
side with each `T.jumpSet i` in the union of `[-η, η]` and the opposite far window
`-ε i • [b i, b i + W]`, and let `P` be a pairing of the lattices of `T` and `S`. For `c` in
`T.paramLattice` and `d` in `V`, the cup product under `P` of the cocycles `T.cocycleMap c` and
`S.cocycleMap d` is the coboundary of a continuous cochain, for every topology on `Γ` that makes
the map to `G_p` an open embedding: this is `P.IsScaledCupCoboundary 0 c d`, the exponent `0`
saying that `S.cocycleMap d` need not be multiplied by a power of `p`. -/
lemma exists_relLength_le_and_isScaledCupCoboundary (D : FewLowJumpsData S) :
    ∃ V : Submodule ℤ_[p] S.paramLattice,
      relLength (⊤ : Submodule ℤ_[p] S.paramLattice) V ≤
        (∑ i : k.Letter, (D.n i * (8 * D.a + 1) + D.r i * (3 * (D.W + 1))) : ℕ) ∧
      ∀ (T : k.PairingSide O) (P : T.SidePairing S) (c : T.paramLattice),
        (∀ i : k.Letter, FitsWindows D.η (-D.ε i) (D.b i) D.W (T.jumpSet i)) →
        ∀ d ∈ V, P.IsScaledCupCoboundary 0 c d := by
  -- `V` is the set of `d` whose part at each letter `i` lies in the module of
  -- `relLength_constantAt_deepConstants_le`. For `d ∈ V` both sides have standard points at every
  -- letter, and the walk applies: the stop is the point of `T` where `ε i = 1`, else that of `S`.
  let δ (i : Letter) := fewLowJumpsDepth D.a D.η D.W (D.b i) (D.ε i)
  refine ⟨⨅ i : Letter, (S.deepConstants i 0 (δ i)).comap (S.constantAt i),
    D.relLength_iInf_comap_deepConstants_le, fun T P c hT_window d hd ↦ ?_⟩
  -- `T` has deep points at every letter, and `E ^ a` kills the cokernels of the Tate dual side.
  choose x hx using fun i ↦ Nat.sub_zero D.a ▸
    D.pointsOver_raisedOrdersAtZero_nonempty_of_fitsWindows (i := i) hT_window 0 c
  choose x' hx' using (fun i : Letter ↦ by
    obtain ⟨y, ⟨hy_exp, -, hy_deep⟩, hy_const⟩ := (mem_iInf _).1 hd i
    exact ⟨y, y.prop, by simpa using hy_const, hy_exp, hy_deep⟩
    : ∀ i : Letter, ∃ x' : S.extensionLattice.Ambient,
        x' ∈ S.pointsOver d i 0 (raisedOrdersAtZero 0) (δ i))
  have h_kill (i : Letter) : P.tateDualSide.KillsCokernel i 0 D.a :=
    killsCokernel_of_isUnramified 0 D.a
      (by simpa only [zero_add] using D.tateDualSide_jump_le P hT_window) D.hk D.hp
  -- No jump of `T` lies in `[-a, -η)`, so its points have a pole of order at most `η`.
  have hx_plain (i : Letter) :
      x i ∈ T.pointsOver c i 0 (raisedOrdersAtZero (-D.η)) (plainDepth D.a D.η 1 0) :=
    mem_pointsOver_of_le (mem_pointsOver_raisedOrdersAtZero_of_gap (t := D.a) (hx i)
      (natCast_nonneg D.η) (fun u hu _ ↦ by
        have := D.hb_gt i; obtain _ | _ | _ := low_or_far_of_fitsWindows (hT_window i) hu <;> omega)
      (fun _ _ _ ↦ by simp only [improvedOrders, raisedOrdersAtZero]; split_ifs <;> omega)
      fun l u _ ↦ raisedOrdersAtZero_mono (by omega) l u)
      (fun _ _ _ ↦ le_rfl) fun _ _ _ ↦ by
        simp only [plainDepth, standardDepth, raisedOrdersAtZero]; omega
  have hx'_standard (i : Letter) : x' i ∈ S.standardPoints d i 0 D.a D.η 1 := by
    refine mem_pointsOver_of_le (hx' i) (fun l u _ ↦ raisedOrdersAtZero_mono (by omega) l u)
      fun l u hu ↦ ?_
    have hu_ge : l = 0 → -u ≤ D.b i + D.W := by
      rintro rfl; have := D.hb_gt i
      obtain _ | _ | _ := low_or_far_of_fitsWindows (D.h_window i) hu <;> omega
    simp only [δ, fewLowJumpsDepth, ite_apply, standardDepth, raisedOrdersAtZero,
      negativeWindowDepth]; lia
  refine P.isScaledCupCoboundary_of_stops_at_all_letters x x' h_kill
    (fun i ↦ mem_standardPoints_of_plainDepth (hx_plain i)) hx'_standard (fun i ↦ ?_) le_rfl
  exact (D.toOpposite P hT_window).hasStop_one_of_neg (h_kill i) (hx_plain i) (hx'_standard i)
    (hx' (i.stepBack 1)) fun hε _ h_down ↦
      ⟨x' i, mem_stopPoints_of_down one_pos (forall_mem_U_stepBack_of_lt_one h_down)
        (hx'_standard i), D.isSafeMoveFst_of_negativeWindowDepth P hT_window (hx i)
        (hx (i.stepBack 1)) (by
          have hne : D.ε i ≠ 1 := by rw [show D.ε i = -1 from hε]; decide
          simpa only [δ, fewLowJumpsDepth, hne, ite_false] using hx' i)⟩

end DeepConstants

end New.Lift.KummerChart.PairingSide

end FewLowJumps
