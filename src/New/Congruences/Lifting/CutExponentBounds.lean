module

public import New.Congruences.Lifting.LongGap
public import New.Congruences.Lifting.SafeMoves

/-!
# Exponent bounds by cuts for paired sides of a Kummer chart: sparse thick letters, two sizes

This file concerns two paired sides `S`, `S'` over a Kummer chart, whose distinguished element is
written `E`. Letters `i : k.Letter` are permuted by Frobenius `k.letterFrob`. The jumps
`S.jumpSet i`, `S'.jumpSet i` lie in `[-η, η] ∪ ∓ε i • [β i, β i + V]` (`New.Lift.FitsWindows`),
with opposite far windows, and `V + 4η ≤ W`. A cut a bounded number of letters back from each
letter then gives the bound for the exponent in `New.Lift.Pairing.IsScaledCupCoboundary`; two
choices of cuts treat the cases of two sizes of far windows: one where the thick letters, those
with the larger size, are sparse, and one where they form any pattern.

## Main definitions and results

* `New.Lift.KummerChart.PairingSide.killsCokernel_of_isKillingCut`: at a cut `i`, `p ^ κ * E ^ s i`
  kills the cokernel.
* `New.Lift.KummerChart.PairingSide.SidePairing.exists_stop_of_hasSignBefore`,
  `New.Lift.KummerChart.PairingSide.SidePairing.exists_stop_of_isLongGap`: the stop of the walk at a
  plain cut and at a cut with a long gap.
* `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_of_cut_windows`: the scheme.
  It derives the bound from a cut 1 to `2J + 1` letters back from each letter.
* `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_sparse_thick`,
  `New.Lift.KummerChart.PairingSide.SidePairing.isScaledCupCoboundary_any_pattern`: two choices of
  cuts and constants.

Notions from other files:
* `New.Lift.KummerChart`: a ring `k.S` = Λ⟦z⟧ in A_inf, where Λ = `WittFq k.f` = W(𝔽_{p^f}), and a
  subgroup Γ' of Γ of index prime to p that fixes Λ. It is unramified (`IsUnramified`) if E = z + p
  and the ramification index `k.e` is 1. The number `k.differentBound` is 0 if `k.e = 1` and
  v_p(e) + 1 otherwise.
* `New.Lift.KummerChart.Coeffs`: a ring of coefficients O, a finite free Z_p-algebra with an element
  ζ such that ζ^{p^f−1} = 1; ζ cuts out the letters.
* `New.Lift.KummerChart.Letter`: the letters of a Kummer chart, that is, the multiplicative group of
  the field with p^f elements in the tilt of the ring of integers of C_p; `i.stepBack a` is the
  letter `a` Frobenius steps back.
* `New.Lift.KummerChart.PairingSide`, `New.Lift.KummerChart.PairingSide.KillsCokernel`: one side
  of a pairing: lattices Y and C (`paramLattice`), an O-linear map `cocycleMap` from C to the
  crystalline cocycles Z_f(Y), and for each letter a finite set of integers that contains 0, the
  jumps. The extension `extensionLattice` of C by Y maps by `projTrivial` to `trivialLattice`, the
  lattice C with trivial action. `KillsCokernel`: `p ^ κ * E ^ s` multiplies the part of A_inf ⊗ C
  at a letter into the image of the standard module of level 0 of the extension.
* `New.Lift.KummerChart.PairingSide.pointsOver`: `S.pointsOver c i e o d` is the set of the vectors
  `x` of the Kisin module of the extension, with all φ^a E inverted, that lie over `p ^ e c` at `i`,
  have the orders `o` and have the depth `d`: every `g • x - x` with `g` in Γ' has exponents `d`.
* `New.Lift.raisedOrdersAtZero`: the orders `raisedOrdersAtZero t` are `-u` on the jump `u`, raised
  by `t` at E. The vectors with orders `raisedOrdersAtZero (-s)` have a pole of order at most `s` at
  E.
* `New.Lift.Pairing.IsSafeMoveFst`, `New.Lift.Pairing.IsSafeMoveSnd`: one side moves by a vector
  while the other rests at a point `x`. The move is safe for `κ` if, for all `g` in Γ', `p ^ κ`
  times the pairing of `g • x - x` with the move (for the second side, with `g` times the move) lies
  in the image of W(𝔪^♭).

## Relation to the literature

Take crystalline lattices with weights in short windows near 0 and near large weights, in the cases
of no small negative weight, two sizes, or sparse large weights. For these, an explicit power of p,
independent of the rank, makes crystalline classes cup to zero with those of congruent dual
lattices. This bounds the loss at the places above p in the Selmer bound. The case of small weights
and a rank-free factorial torsion bound by Sen operators are known in the literature. Related work:
Gao–Liu, Integral filtered Sen theory and applications, 2024; Iovita–Marmora, Continuity of the
finite Bloch–Kato cohomology, 2015; Y. Min, Congruences of first syntomic cohomology groups, 2026.
-/

@[expose] public section

namespace New.Lift.KummerChart

section SparseThickLetters

open Period Finset

variable {p : ℕ} [j : ThePrime p] [Γ : GroupOverGp p] {k : KummerChart Γ}

/-- The letter `i.stepBack l` is the nearest cut before `i`. -/
structure Letter.IsNearestCut (i : k.Letter) (cut : k.Letter → Prop) (l : ℕ) : Prop where
  /-- The cut is at least one step back. -/
  pos : 0 < l
  /-- The letter `l` steps back is a cut. -/
  cut_stepBack : cut (i.stepBack l)
  /-- No letter strictly between it and `i` is a cut. -/
  not_cut : ∀ a ∈ Set.Ioo 0 l, ¬cut (i.stepBack a)

/-- None of the `J` letters after `i` satisfies `T`. -/
def Letter.HasThinSuccessors (i : k.Letter) (T : k.Letter → Prop) (J : ℕ) : Prop :=
  ∀ t ≥ 1, t ≤ J → ¬T ((k.letterFrob ^ t) i)

/-- Suppose that no three letters with `T` follow one another with both gaps between `1` and `J`.
If `i.stepBack r` satisfies `T` and does not have thin successors, that is, one of the `J` letters
after it satisfies `T` too, then `i.stepBack (r + (J + 1))` has thin successors: none of the `J`
letters before `i.stepBack r` satisfies `T`. -/
lemma Letter.hasThinSuccessors_stepBack_add {T : k.Letter → Prop} {J : ℕ}
    (h_sparse : ∀ i : k.Letter, ∀ s ∈ Icc 1 J, ∀ t ∈ Icc 1 J,
      T i → T ((k.letterFrob ^ s) i) → ¬T ((k.letterFrob ^ (s + t)) i))
    (i : k.Letter) (r : ℕ) (h_after : ¬(i.stepBack r).HasThinSuccessors T J)
    (h_thick : T (i.stepBack r)) :
    (i.stepBack (r + (J + 1))).HasThinSuccessors T J := fun n hn_pos hn h_before ↦
  h_after fun t ht_pos ht ↦ by
    set j := (k.letterFrob ^ n) (i.stepBack (r + (J + 1))) with hj
    have h_letters : (k.letterFrob ^ (J + 1 - n)) j = i.stepBack r := by
      simp [hj, pow_add, pow_sub _ (hn.trans J.le_succ)]
    have h_not := h_sparse j (J + 1 - n) (mem_Icc.2 ⟨by omega, by omega⟩) t
      (mem_Icc.2 ⟨ht_pos, ht⟩) h_before (by rwa [h_letters])
    rwa [add_comm, pow_add, Equiv.Perm.mul_apply, h_letters] at h_not

/-- The parameters and size conditions of a scheme of cuts on a Kummer chart `k`, for shifts `s i`,
far windows of width `V` starting at `β i` with signs `ε i`, low-window radius `η`, and padded
width `W ≥ V + 4 η`. The shifted far windows end at or below `2 b`, and `G` bounds `β + W` at the
`J` letters after a thin cut (`CutScheme.IsKillingCut.of_thin`). Also `n` bounds `G / (p - 1)`,
`s₀` bounds `(β i + W) / (p - 3)` if `p ≥ 5`, `ω` bounds windows before a long-gap pivot, `X` is
the cost of one letter or level, `δ` the cost of depth `2 b`, and `p ^ κ` is the killer at a cut.
Here `k.differentBound` is `0` if `k.e = 1`, and `v_p(k.e) + 1` otherwise. -/
structure CutScheme (k : KummerChart Γ) where
  /-- The pole shift at each letter. -/
  s : k.Letter → ℕ
  /-- The start of the far window at each letter. -/
  β : k.Letter → ℕ
  /-- The sign of the far window of the second side at each letter. -/
  ε : k.Letter → ℤˣ
  /-- The radius of the low window `[-η, η]`. -/
  η : ℕ
  /-- The width of the far windows. -/
  V : ℕ
  /-- The padded width `W ≥ V + 4 η`. -/
  W : ℕ
  /-- The unit of cost per level. -/
  X : ℕ
  /-- The cost of depth `2 b`. -/
  δ : ℕ
  /-- The cokernel killer exponent at cuts. -/
  κ : ℕ
  /-- Half of the global shifted-window height bound `2 b`. -/
  b : ℕ
  /-- The thin-window bound unit (`G ≤ (p - 1) n`). -/
  n : ℕ
  /-- The sparsity/gap parameter `J`. -/
  J : ℕ
  /-- The unramified pole bound `s₀`. -/
  s₀ : ℕ
  /-- The bound on `β + W` at the `J` letters after a thin cut. -/
  G : ℕ
  /-- The window bound before the pivot of a long gap. -/
  ω : ℕ
  /-- The low-window radius is at least `1`. -/
  hη : 1 ≤ η
  /-- The padded width satisfies `V + 4 η ≤ W`. -/
  hW : V + 4 * η ≤ W
  /-- The shifted width satisfies `s i + W ≤ p n`. -/
  h_shift : ∀ i : k.Letter, s i + W ≤ p * n
  /-- The unit of cost `X` is large against `n`, `log_p (2 b)`, `W` and `G`. -/
  le_cost : n + p.log (2 * b) + (J + 1 + k.differentBound) * W + k.differentBound * G ≤ X
  /-- The exponent `κ` exceeds `12 ((J + 1) X + δ)`. -/
  cost_lt : 12 * ((J + 1) * X + δ) < κ
  /-- The depth `2 b` times the ramification index is at most `p ^ (J + 1) δ`. -/
  ramification_mul_le : k.e * (2 * b) ≤ p ^ (J + 1) * δ
  /-- The ramification index is at most `p ^ (J + 1) / 8`. -/
  ramification_le : 8 * k.e ≤ p ^ (J + 1)
  /-- The shifted far windows end at or below `2 b`. -/
  far_le : ∀ i : k.Letter, β i + s i + W ≤ 2 * b
  /-- The bound `G` is at most `(p - 1) n`. -/
  thin_le : G ≤ (p - 1) * n
  /-- For `p ≥ 5` the far windows end at or below `(p - 3) s₀`. -/
  far_le_of_five_le : 5 ≤ p → ∀ i : k.Letter, β i + W ≤ (p - 3) * s₀

/-- Each of the `l` letters `i.stepBack a` with `a < l` has the sign `ρ`, or its far window
`[β, β + V]` ends at or below `η`. -/
def CutScheme.HasSignBefore (C : k.CutScheme) (i : k.Letter) (l : ℕ) (ρ : ℤˣ) : Prop :=
  ∀ a < l, C.ε (i.stepBack a) = ρ ∨ C.β (i.stepBack a) + C.V ≤ C.η

/-- A long gap at the pivot `i.stepBack t`, one of the `l` letters after `i.stepBack l` up to `i`:
the far window of the pivot starts far out, and the other letters have the opposite sign or small
far windows. The number `C.ω` bounds the low window and the far windows before the pivot. -/
structure CutScheme.IsLongGap (C : k.CutScheme) (i : k.Letter) (l t : ℕ) : Prop where
  /-- The chart is unramified. -/
  isUnramified : k.IsUnramified
  /-- The prime is at least `5`. -/
  five_le : 5 ≤ p
  /-- The letter `l` steps back has shift `0`. -/
  shift_eq_zero : C.s (i.stepBack l) = 0
  /-- The pivot is `J + 1` letters after `i.stepBack l`. -/
  pivot_add : t + (C.J + 1) = l
  /-- The far window of the pivot starts beyond `s₀ + ω (1 + p + ⋯ + p ^ J)`. -/
  lt_far_pivot : C.s₀ + C.ω * ∑ a ∈ range (C.J + 1), p ^ a < C.β (i.stepBack t)
  /-- The other letters have the opposite sign, or a far window that ends at or below `η`. -/
  sign_ne_or_far_le :
    ∀ a < l, a ≠ t → C.ε (i.stepBack a) ≠ C.ε (i.stepBack t) ∨ C.β (i.stepBack a) + C.V ≤ C.η
  /-- The low window ends at or below `ω`. -/
  low_le : C.η ≤ C.ω
  /-- The far windows of the letters before the pivot end at or below `ω`. -/
  far_le : ∀ a < l, t < a → C.β (i.stepBack a) + C.V ≤ C.ω

/-- The two kinds of letters `i` at which `p ^ C.κ * E ^ C.s i` is shown to kill the cokernel. -/
inductive CutScheme.IsKillingCut (C : k.CutScheme) (i : k.Letter) : Prop
  /-- The shift is `0` and the next `J` letters have `β + W ≤ G`. -/
  | of_thin (shift_eq_zero : C.s i = 0)
      (next_le : ∀ t ∈ Icc 1 C.J, C.β ((k.letterFrob ^ t) i) + C.W ≤ C.G)
  /-- The chart is unramified, `p ≥ 5`, and the shift lies in `[s₀ - κ, β i)`. -/
  | of_isUnramified (shift_lt : C.s i < C.β i) (isUnramified : k.IsUnramified) (five_le : 5 ≤ p)
      (le_add_shift : C.s₀ ≤ C.κ + C.s i)

/-- If `i` satisfies `C.IsKillingCut i`, then either the shift `C.s i` is `0`, or `C.s i < C.β i`
and `k.differentBound = 0`. -/
lemma CutScheme.IsKillingCut.shift_eq_zero_or_lt {C : k.CutScheme} {i : k.Letter}
    (h_cut : C.IsKillingCut i) : C.s i = 0 ∨ C.s i < C.β i ∧ k.differentBound = 0 := by
  obtain h_zero | ⟨h_lt, ⟨-, -, h_diff⟩⟩ := h_cut
  exacts [.inl h_zero, .inr ⟨h_lt, h_diff⟩]

/-- The exponents of the standard point at a cut with shift `s`, where the cut before is `l` steps
back. The point has the exponents `raisedOrdersAtZero (-s)` (`-u`, lowered by `s` at the level `0`)
and the depth `standardDepth s η (l + 1)` (`-u`, raised by `s` at the level `0` and by `η` at the
levels up to `l`). This depth improves the exponents: they become the depth where they were
positive, and the minimum of the depth and `0` elsewhere (`JumpLattice.improvedOrders`). -/
def cutOrders (s η l : ℕ) : ℕ → ℤ → ℤ :=
  JumpLattice.improvedOrders (raisedOrdersAtZero (-s)) (PairingSide.standardDepth s η (l + 1))

/-- The depth of the point at which a side rests when the walk meets a cut with a long gap: `r` at
the level `t` of the pivot, `1` at the other levels below `l`, and `-u` beyond. -/
def longGapDepth (l t r a : ℕ) (u : ℤ) : ℤ :=
  if a = t then r else if a < l then 1 else -u

/-- The steps that may be needed to deepen a point at `i` of a side whose far windows have the
signs `σ`: two windows, around `0` and `∓ β`, at each of the first `2 J + 2` levels. -/
noncomputable def CutScheme.windowSteps (C : k.CutScheme) (i : k.Letter) (σ : k.Letter → ℤˣ) :
    Finset (Σ _ : ℕ, ℤ) :=
  (range (2 * C.J + 2)).sigma fun a ↦ twoWindows ((if a = 0 then C.s i else 0) + C.W)
    ((if σ (i.stepBack a) = 1 then -1 else 1) * C.β (i.stepBack a))

/-- The steps `C.windowSteps i σ` are the pairs `(a, m)` of a level `a < 2 J + 2` and an integer
`m` near `0` or near `-σ j • β j`, where `j = i.stepBack a` and `σ j` is any sign; near means
within `s i + W` at the level `0` and within `W` at the others. The step `(a, m)` costs
`k.cost a m = v_p(m) + d + 3 a`, with `v_p(0) = 0` and `d = k.differentBound`, which is `0` if the
ramification index `k.e` is `1` and `v_p(k.e) + 1` otherwise. Under the size conditions of `C`,
if `s i` or `d` is `0`, the steps then cost at most `5 κ - 4 δ` together. -/
lemma CutScheme.sum_cost_windowSteps_le (C : k.CutScheme) {σ : k.Letter → ℤˣ} {i : k.Letter}
    (h_zero : C.s i = 0 ∨ k.differentBound = 0) :
    C.κ + 4 * C.δ + ∑ q ∈ C.windowSteps i σ, k.cost q.1 q.2 ≤ 6 * C.κ := by
  -- By `sum_twoWindows_le` each of the `2 J + 2` levels costs at most `30 X`.
  have h_level (a : ℕ) (ha : a ∈ range (2 * C.J + 2)) :
      ∑ m ∈ twoWindows ((if a = 0 then C.s i else 0) + C.W)
        ((if σ (i.stepBack a) = 1 then -1 else 1) * C.β (i.stepBack a)), k.cost a m ≤ 30 * C.X := by
    -- The shift `r` occurs only at the level `0`, where it is `0` or the steps cost only `v_p(m)`.
    obtain ⟨r, hr, hr_le, hr_zero⟩ : ∃ r : ℕ, (if a = 0 then C.s i else 0) = r ∧
        r ≤ min (C.s i) (C.s (i.stepBack a)) ∧ (r = 0 ∨ k.differentBound + 3 * a = 0) := by
      obtain rfl | ha_pos := a.eq_zero_or_pos
      exacts [⟨C.s i, rfl, (min_self _).ge, h_zero⟩,
        ⟨0, ite_eq_right ha_pos.ne', Nat.zero_le _, .inl rfl⟩]
    have h_rest : (4 * (r + C.W) + 2) * (k.differentBound + 3 * a) ≤
        5 * C.W * (6 * (C.J + 1 + k.differentBound)) := by
      rw [mem_range] at ha
      obtain rfl | h_free := hr_zero
      · exact Nat.mul_le_mul (by have := C.hη; have := C.hW; omega) (by omega)
      · simp [h_free]
    rw [hr]
    calc _ ≤ 8 * C.n + 2 * p.log (2 * C.b) + (4 * (r + C.W) + 2) * (k.differentBound + 3 * a) :=
          sum_twoWindows_le (Fact.out : p.Prime) C.n (2 * C.b) (by have := C.h_shift i; omega)
            (by have := C.far_le (i.stepBack a)
                have : |(if σ (i.stepBack a) = 1 then -1 else 1) * (C.β (i.stepBack a) : ℤ)| =
                  C.β (i.stepBack a) := by simp [apply_ite]
                omega)
      _ ≤ 30 * C.X := by linarith [C.le_cost, Nat.zero_le (k.differentBound * C.G)]
  have h_sum : ∑ q ∈ C.windowSteps i σ, k.cost q.1 q.2 ≤ (2 * C.J + 2) * (30 * C.X) := by
    simpa [CutScheme.windowSteps, sum_sigma] using sum_le_card_nsmul _ _ _ h_level
  linarith [C.cost_lt]

/-- A set that lies in the union of the low window `[-η, η]` and a far window `± [b, b + V]` is
bounded above by `b + W` if `V + η ≤ W`. -/
lemma _root_.New.Lift.FitsWindows.le_add {η b V W : ℕ} {ρ : ℤˣ} {U : Finset ℤ}
    (hU : FitsWindows η ρ b V U) (hW : V + η ≤ W) {u : ℤ} (hu : u ∈ U) : u ≤ b + W := by
  obtain h_low | h_pos | h_neg := hU u hu <;> omega

namespace PairingSide

variable {O : k.Coeffs} {S S' : PairingSide O}

/-- Package paired sides fitting a `CutScheme` into `OppositeWindowSides`. -/
def _root_.New.Lift.KummerChart.CutScheme.toOpposite (C : k.CutScheme) (h : S.SidePairing S')
    (hU : ∀ i : k.Letter, FitsWindows C.η (-C.ε i) (C.β i) C.V (S.jumpSet i))
    (hU' : ∀ i : k.Letter, FitsWindows C.η (C.ε i) (C.β i) C.V (S'.jumpSet i)) :
    OppositeWindowSides h :=
  ⟨C.η, C.V, C.β, C.ε, hU, hU'⟩

/-- Let `S` be a side whose jumps at each letter `i` are at most `β i + W`. Let the size conditions
`CutScheme` hold: `β + s + W ≤ 2 b` for the shifts `s`, the cost `X` is large against `n`, `W` and
`G`, with `G ≤ (p - 1) n`, the depth `2 b` costs `δ` over `J + 1` letters, and
`κ > 12 ((J + 1) X + δ)` (`s₀` plays no part). If `β + W ≤ G` at the `J` letters after `i`, then
`p ^ κ` kills the cokernel at `i`: it multiplies `A_inf ⊗ C`, for the lattice
`C = S.paramLattice`, into the image of the extension of level `0`. -/
lemma killsCokernel_zero_of_next_le (C : k.CutScheme)
    (h_jump : ∀ i : k.Letter, ∀ u ∈ S.jumpSet i, u ≤ C.β i + C.W) {i : k.Letter}
    (h_next : ∀ t ∈ Icc 1 C.J, C.β ((k.letterFrob ^ t) i) + C.W ≤ C.G) :
    S.KillsCokernel i C.κ 0 := by
  -- All jumps are at most `2 b` and those at the `J` letters after `i` are at most `G`. The size
  -- conditions bound the three terms of the cokernel bound with weights by multiples of `X`, `δ`.
  refine killsCokernel_zero_of_jumps_le (ω := 2 * C.b)
    (fun i' u hu ↦ by have := C.far_le i'; have := h_jump i' u hu; omega)
    (fun t ht u hu ↦ (h_jump _ u hu).trans (mod_cast h_next t ht)) C.ramification_le ?_
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have h_step : k.differentBound * C.G + C.n ≤ C.X := by
    linarith only [C.le_cost, Nat.zero_le ((C.J + 1 + k.differentBound) * C.W)]
  have h_thin : (C.G : ℝ) / (p - 1) ≤ C.X := by
    rw [div_le_iff₀' (sub_pos.2 (mod_cast hp)), ← Nat.cast_pred (by omega)]
    exact_mod_cast C.thin_le.trans (Nat.mul_le_mul_left _ (le_of_add_le_right h_step))
  have h_depth : (k.e * (2 * C.b : ℕ) : ℝ) / p ^ (C.J + 1) ≤ C.δ :=
    (div_le_iff₀' (by positivity)).2 (mod_cast C.ramification_mul_le)
  calc _ = (2 * C.J * (k.differentBound * C.G) : ℝ) + (2 * C.J + 4) * (C.G / (p - 1)) +
          8 * (k.e * (2 * C.b : ℕ) / p ^ (C.J + 1)) := by ring
    _ ≤ 2 * C.J * C.X + (2 * C.J + 4) * C.X + 8 * C.δ := by
        gcongr; exact_mod_cast le_of_add_le_left h_step
    _ ≤ C.κ := mod_cast (by linarith only [C.cost_lt, Nat.zero_le (C.J * C.X)] :
        2 * C.J * C.X + (2 * C.J + 4) * C.X + 8 * C.δ ≤ C.κ)

/-- The cokernel at a cut of the side `S`. Let its jumps at each letter `i` be at most `β i + W`,
for shifts `s i`, and let the size conditions `CutScheme` hold. Then `p ^ κ * E ^ s i`, with `E` the
distinguished element, kills the cokernel of the extension over `S.paramLattice` at every letter `i`
with `IsKillingCut`: `s i = 0` and the next `J` letters have `β + W ≤ G`, or the chart is
unramified, `p ≥ 5` and `s₀ - κ ≤ s i < β i`. -/
lemma killsCokernel_of_isKillingCut (C : k.CutScheme)
    (h_jump : ∀ i : k.Letter, ∀ u ∈ S.jumpSet i, u ≤ C.β i + C.W) {i : k.Letter}
    (h_cut : C.IsKillingCut i) : S.KillsCokernel i C.κ (C.s i) := by
  cases h_cut with
  | of_thin hs_zero h_next =>
    simpa only [hs_zero] using killsCokernel_zero_of_next_le C h_jump h_next
  | of_isUnramified _ hk hp hs₀ =>
    exact killsCokernel_of_isUnramified C.κ (C.s i)
      (fun i' u hu ↦ (h_jump i' u hu).trans
        (mod_cast (C.far_le_of_five_le hp i').trans (Nat.mul_le_mul_left (p - 3) hs₀))) hk hp

/-- The standard point of a side `S` at a cut `i`. Let the jumps of `S` lie in `[-η, η]` and in the
far windows `σ j • [β j, β j + V]` of signs `σ j`. Let `η ≥ 1`, `V + 4 η ≤ W`, let the shifts `s`
have `s i + W ≤ p n`, let the size conditions `CutScheme` hold, let the cut be of a kind at which
the cokernel is killed, and let `l ≤ 2 J + 1` be its distance to the cut before. Then for `c` in
`S.paramLattice` the extension has a point at `i` over `p ^ H c` for any `H ≥ 6 κ` with the orders
`cutOrders (s i) η l` and with depth `standardDepth (s i) η (l + 1)`: `-u`, raised by `s i` at the
level `0` and by `η` at the levels up to `l`. -/
lemma pointsOver_cutOrders_nonempty (C : k.CutScheme) {H : ℕ} {σ : k.Letter → ℤˣ}
    (hU : ∀ i : k.Letter, FitsWindows C.η (σ i) (C.β i) C.V (S.jumpSet i))
    (hH : 6 * C.κ ≤ H) {i : k.Letter} (h_cut : C.IsKillingCut i) {l : ℕ} (hl : l ≤ 2 * C.J + 1)
    (c : S.paramLattice) :
    (S.pointsOver c i H (cutOrders (C.s i) C.η l)
      (standardDepth (C.s i) C.η (l + 1))).Nonempty := by
  obtain ⟨x, hx⟩ := pointsOver_nonempty_of_killsCokernel
    (killsCokernel_of_isKillingCut C (fun j u ↦ (hU j).le_add (by have := C.hW; omega)) h_cut) c
  have h_cost := C.sum_cost_windowSteps_le (σ := σ) (h_cut.shift_eq_zero_or_lt.imp_right And.right)
  refine pointsOver_nonempty_of_costs hx (C.windowSteps i σ) (fun a u hu m hm_ge hm_lt ↦ ?_)
    (by omega)
  -- The steps lie at the levels up to `l`, within `s i + η` or `η` of `-u`.
  have := C.hW
  simp only [CutScheme.windowSteps, mem_sigma, mem_range, mem_union, mem_Icc, ← Units.val_eq_one]
  grind [raisedOrdersAtZero, standardDepth, hU (i.stepBack a) u hu]

/-- Let the jumps of the side `S` at the letter `i` lie in `[-η, η]` and in the far window
`σ • [β i, β i + V]`, and let `i` be a cut of a kind at which the cokernel is killed, with shift
`s i`. Let `x` be a standard point at `i` over `p ^ e c`: the depth (the orders of all `g • x - x`)
is `standardDepth (s i) η (l + 1)`, that is `-u` raised by `s i` at the level `0` and by `η` at the
levels up to `l`, and the orders `cutOrders (s i) η l` are `-u - s i` at the level `0` and `-u`
above, improved by this depth. As no jump lies in `[-s i, -η)`, the point `x` has the orders
`raisedOrdersAtZero (-η)`, a pole of order at most `η` at the distinguished element `E`, and it has
the depth `plainDepth (s i) η l η` that a cut without long gap asks. -/
lemma mem_pointsOver_plainDepth_of_cutOrders (C : k.CutScheme) {e : ℕ} {σ : ℤˣ} {i : k.Letter}
    {l : ℕ} {c : S.paramLattice} {x : S.extensionLattice.Ambient}
    (hU : FitsWindows C.η σ (C.β i) C.V (S.jumpSet i)) (h_cut : C.IsKillingCut i)
    (hx : x ∈ S.pointsOver c i e (cutOrders (C.s i) C.η l) (standardDepth (C.s i) C.η (l + 1))) :
    x ∈ S.pointsOver c i e (raisedOrdersAtZero (-C.η)) (plainDepth (C.s i) C.η l C.η) := by
  have h_shift := h_cut.shift_eq_zero_or_lt.imp_right And.left
  have h_pole := mem_pointsOver_raisedOrdersAtZero_of_gap (t := C.s i) hx (Int.natCast_nonneg C.η)
    (fun u hu _ ↦ by obtain _ | _ | _ := low_or_far_of_fitsWindows hU hu <;> omega)
    (fun _ _ _ ↦ by
      simp only [cutOrders, JumpLattice.improvedOrders, raisedOrdersAtZero, standardDepth]
      split_ifs <;> omega)
    fun _ _ _ ↦ by grind [raisedOrdersAtZero, standardDepth]
  exact mem_pointsOver_of_le h_pole (fun _ _ _ ↦ le_rfl) fun _ _ _ ↦ by
    simp only [plainDepth, standardDepth]; omega

/-- The stop at `i` when the nearest cut before it, `i.stepBack l` (`l` letters back), is followed
by a long gap. Let `S` have its jumps in `[-η, η]` and in far windows of width `V` at `β` with signs
`σ`. The long gap at the pivot `i.stepBack t`, `J + 1` letters after the cut, means that its far
window starts beyond `s₀ + ω (1 + ⋯ + p ^ J)`, where `ω` bounds the windows before it; its signs
`ε` are not tied to `σ`. Let `σ` be `-1` at the pivot, and let the jumps at the other letters after
the cut be at least `-η`. Let the size conditions hold: `2 b` bounds the shifted far windows
`β + s + W`, `G` the windows of the `J` letters after a thin cut, `n` bounds `G / (p - 1)`, and
`κ` is large against the costs. Let `η ≥ 1`, `V + 4 η ≤ W`, `s i + W ≤ p n`, `l ≤ 2 J + 1`, and let
the cut be of a kind at which the cokernel is killed. Then `S` has a point over `p ^ H c` for any `H ≥ 6 κ`, at
which it can rest (a stop): its orders `stopOrders η l` are `max 0 (-u - η)` below the level `l` and
`-u` from `l` on, and its depth `longGapDepth l t (2 b)` is `2 b` at the level `t`, `1` at the
others below `l` and `-u` from `l` on. -/
lemma pointsOver_longGapDepth_nonempty (C : k.CutScheme) {H : ℕ} {σ : k.Letter → ℤˣ}
    (hU : ∀ i : k.Letter, FitsWindows C.η (σ i) (C.β i) C.V (S.jumpSet i))
    (hH : 6 * C.κ ≤ H) {i : k.Letter} {l t : ℕ} (hl : l ≤ 2 * C.J + 1)
    (h_cut : C.IsKillingCut (i.stepBack l)) (h_gap : C.IsLongGap i l t)
    (h_pivot : σ (i.stepBack t) = -1)
    (h_up : ∀ a : ℕ, a < l → a ≠ t → ∀ u ∈ S.jumpSet (i.stepBack a), -C.η ≤ u)
    (c : S.paramLattice) :
    (S.pointsOver c i H (stopOrders C.η l) (longGapDepth l t (2 * C.b))).Nonempty := by
  -- The long gap gives a point over `p ^ (κ + 4 δ)` of depth `2 b` at the pivot. Carry it to `i` by
  -- `φ ^ t`, and raise its depth from `0` to `1` at the levels between `t` and `l`.
  obtain ⟨hk, hp, hs_cut, rfl, h_long, -, h_low, h_thin⟩ := h_gap
  have hW_le := C.hW
  have h_jump (j : k.Letter) (u : ℤ) (hu : u ∈ S.jumpSet j) : u ≤ C.β j + C.W :=
    (hU j).le_add (by omega) hu
  have h_back (a : ℕ) : (i.stepBack t).stepBack a = i.stepBack (t + a) := by simp [pow_add]
  have h_small (a : ℕ) (ha : a < C.J + 1) (u : ℤ)
      (hu : u ∈ S.jumpSet ((i.stepBack t).stepBack a)) : u ≤ C.ω := by
    obtain rfl | ha_pos := a.eq_zero_or_pos
    · exact (jump_le_of_fitsWindows (hU _) (.inl h_pivot) u hu).trans (mod_cast h_low)
    · rw [h_back] at hu
      have := h_thin (t + a) (by omega) (by omega)
      obtain _ | _ | _ := low_or_far_of_fitsWindows (hU _) hu <;> omega
  obtain ⟨x, hx⟩ := pointsOver_nonempty_of_long_gap (N := C.s₀ + C.ω * ∑ a ∈ range (C.J + 1), p ^ a)
    hk ((by omega : 3 ≤ p).trans (Nat.le_self_pow C.J.succ_ne_zero p))
    (by simpa [hk.2.1] using C.ramification_mul_le)
    (by simpa only [h_back, hs_cut] using killsCokernel_of_isKillingCut C h_jump h_cut)
    (killsCokernel_of_isUnramified 0 C.s₀ (fun j u hu ↦ (h_jump j u hu).trans
      (by simpa using mod_cast C.far_le_of_five_le hp j)) hk hp)
    h_small rfl (by have := C.far_le (i.stepBack t); omega) c
  -- The point `φ ^ t • x` at `i` has the exponents and depth of `x`, shifted up by `t` levels.
  refine (pointsOver_nonempty_of_costs (phi_pow_smul_mem_pointsOver (l := t) hx) (C.windowSteps i σ)
    (fun a u _ m hm_ge hm_lt ↦ ?_)
    ((C.sum_cost_windowSteps_le (σ := σ) (i := i) (.inr hk.2.2)).trans hH)).mono fun y hy ↦
    mem_pointsOver_of_le hy (fun a u hu ↦ ?_) fun _ _ _ ↦ le_rfl
  · -- The only steps are `(a, 0)` with `t < a < l`.
    simp only [CutScheme.windowSteps, JumpLattice.shiftedOrders, JumpLattice.shiftedStdOrders,
      stdOrders, longGapDepth, mem_sigma, mem_range, mem_union, mem_Icc] at hm_ge hm_lt ⊢
    omega
  · -- At the pivot no jump lies in `[-N, -η)`; at the other levels below `l` the side is up.
    have h_far_pivot := C.far_le (i.stepBack t)
    have h_window : a = t → -C.η ≤ u ∨ C.β (i.stepBack t) ≤ -u ∧ -u ≤ C.β (i.stepBack t) + C.V := by
      rintro rfl; obtain _ | _ | _ := low_or_far_of_fitsWindows (hU _) hu <;> omega
    have h_up_level : a < t + (C.J + 1) → a ≠ t → -C.η ≤ u := fun ha hat ↦ h_up a ha hat u hu
    simp only [stopOrders, JumpLattice.improvedOrders, JumpLattice.shiftedOrders,
      JumpLattice.shiftedStdOrders, stdOrders, longGapDepth]
    omega

/-- The inequality that makes a move safe at a cut with a long gap. The move has the minimum of the
exponents `cutOrders s η l` and of `cutOrders 0 η l₀` shifted up by `l` levels (`0` below `l`).
The side at rest has the depth `longGapDepth l t r`, where `t < l` and `0 < r`. At the level `a` let
`u ≤ η` if `t ≠ a < l` and `u < η + r` if `a = t`. Then for every `v` the exponent at `u` and the
depth at `v` add up to at least `ruleBound l 0 a (u + v)`, which is `1` for `a < l` and `-(u + v)`
for `a ≥ l`. -/
lemma ruleBound_le_inf_add_longGapDepth {η l l₀ t r s a : ℕ} {u : ℤ} (ht : t < l) (hr : 0 < r)
    (h_down : a < l → a ≠ t → u ≤ η) (h_pivot : a = t → u < η + r) (v : ℤ) :
    ruleBound l 0 a (u + v) ≤
      (cutOrders s η l ⊓ JumpLattice.shiftedOrders l 0 (cutOrders 0 η l₀)) a u +
        longGapDepth l t r a v := by
  simp only [Pi.inf_apply, ruleBound, cutOrders, JumpLattice.improvedOrders,
    JumpLattice.shiftedOrders, raisedOrdersAtZero, standardDepth, longGapDepth]
  omega

/-- Let the side `R`, which moves first to a stop and rests there, have jumps in `[-η, η]` and in
far windows `σ j • [β j, β j + V]`, and let the other side `R'` have those of signs `-σ`. Let
`η ≥ 1`, `V + 4 η ≤ W`, `s i + W ≤ p n`, let the size conditions hold, and let the letter
`l ≤ 2 J + 1` steps before `i` be a cut at which the cokernel is killed, followed by a long gap with
pivot `i.stepBack t` where `σ` is `-1`. Let the far windows at the levels `a ≠ t` below `l` be small
or of the sign opposite to that at the pivot. Then `R` has a point `q` over `p ^ H c` for any `H ≥ 6 κ`, with
orders `stopOrders η l` and depth `longGapDepth l t (2 b)` that has this property: `R'` moves from
`φ ^ l` of its standard point at that cut, whose own cut before is any `l₀` letters back, to its
standard point at `i`, so the move has the minimum of the two systems `cutOrders`; at each jump `u`
of `R'` this order and the depth at any `v` add up to at least `ruleBound l 0`. -/
lemma exists_mem_pointsOver_ruleBound_le_of_isLongGap (C : k.CutScheme) {H : ℕ}
    {R R' : PairingSide O} {σ : k.Letter → ℤˣ}
    (hR : ∀ i : k.Letter, FitsWindows C.η (σ i) (C.β i) C.V (R.jumpSet i)) (hH : 6 * C.κ ≤ H)
    {i : k.Letter} {l l₀ t : ℕ} (hl : l ≤ 2 * C.J + 1) (h_cut : C.IsKillingCut (i.stepBack l))
    (h_gap : C.IsLongGap i l t) (h_pivot : σ (i.stepBack t) = -1)
    (hR' : ∀ i : k.Letter, FitsWindows C.η (-σ i) (C.β i) C.V (R'.jumpSet i))
    (h_sign : ∀ a < l, a ≠ t →
      σ (i.stepBack a) ≠ σ (i.stepBack t) ∨ C.β (i.stepBack a) + C.V ≤ C.η) (c : R.paramLattice) :
    ∃ q ∈ R.pointsOver c i H (stopOrders C.η l) (longGapDepth l t (2 * C.b)),
      ∀ a : ℕ, ∀ u ∈ R'.jumpSet (i.stepBack a), ∀ v : ℤ, ruleBound l 0 a (u + v) ≤
        (cutOrders (C.s i) C.η l ⊓ JumpLattice.shiftedOrders l 0 (cutOrders 0 C.η l₀)) a u +
          longGapDepth l t (2 * C.b) a v := by
  have h_opposite (a : ℕ) (ha : a < l) (hat : a ≠ t) :
      σ (i.stepBack a) = 1 ∨ C.β (i.stepBack a) + C.V ≤ C.η := by
    simpa only [h_pivot, Int.units_ne_iff_eq_neg, neg_neg] using h_sign a ha hat
  obtain ⟨q, hq⟩ := pointsOver_longGapDepth_nonempty C hR hH hl h_cut h_gap h_pivot
    (fun a ha hat ↦ neg_le_jump_of_fitsWindows (hR _) (h_opposite a ha hat)) c
  refine ⟨q, hq, fun a u hu v ↦ ruleBound_le_inf_add_longGapDepth (by grind [h_gap.pivot_add])
    (by have := C.hη; have := C.hW; have := C.far_le (i.stepBack t); omega)
    (fun ha hat ↦ jump_le_of_fitsWindows (hR' _) ((h_opposite a ha hat).imp_left neg_inj.2) u hu)
    (by -- The jumps at the pivot are less than `η + 2 b`.
      rintro rfl; have := C.hη; have := C.hW; have := C.far_le (i.stepBack a)
      grind [low_or_far_of_fitsWindows (hR' _) hu]) v⟩

/-- Let the sides `S`, `S'`, paired by `h`, have jumps in `[-η, η]` and in opposite far windows
`∓ε j • [β j, β j + V]`. Let the cut `i.stepBack l` have shift `0` and be followed up to `i` by a
long gap: the far window at the pivot `i.stepBack t` starts far out and the others have the opposite
sign or are small. Let `x`, `x'` at `i` and `x₀`, `x₀'` at `i.stepBack l` be points of the two sides
over `p ^ e c`, `p ^ e c'` with the orders `cutOrders` of standard points at these cuts
and any depths `d`, `d₀`. Let `h_cut` say that the cut is of a kind at which the cokernels of `S`
and `S'` are killed, and `h_kill` that `p ^ κ` kills that of the Tate dual side, with lattice
`Hom(Y ⊗ Y', O(1))`, there. Let the size conditions `CutScheme` hold with `η ≥ 1`, `V + 4 η ≤ W`,
`s i + W ≤ p n` and `l ≤ 2 J + 1`. For any `H ≥ 6 κ` one side has a stop at exponent `H`. The other side
moves from `φ ^ l` of its point at `i.stepBack l` to its point at `i`, and this move is safe:
`p ^ κ` times its pairing with all `g • q - q` (`q` the stop) lies in the image of `W(𝔪^♭)`. -/
lemma SidePairing.exists_stop_of_isLongGap (C : k.CutScheme) {e H : ℕ} (h : S.SidePairing S')
    (hU : ∀ i : k.Letter, FitsWindows C.η (-C.ε i) (C.β i) C.V (S.jumpSet i))
    (hU' : ∀ i : k.Letter, FitsWindows C.η (C.ε i) (C.β i) C.V (S'.jumpSet i))
    (hH : 6 * C.κ ≤ H) {i : k.Letter} {l l₀ t : ℕ} (hl : l ≤ 2 * C.J + 1)
    (h_cut : C.IsKillingCut (i.stepBack l))
    (h_kill : h.tateDualSide.KillsCokernel (i.stepBack l) C.κ 0)
    (h_gap : C.IsLongGap i l t) {c : S.paramLattice} {c' : S'.paramLattice}
    {d d₀ : ℕ → ℤ → ℤ} {x₀ x : S.extensionLattice.Ambient} {x₀' x' : S'.extensionLattice.Ambient}
    (hx : x ∈ S.pointsOver c i e (cutOrders (C.s i) C.η l) d)
    (hx' : x' ∈ S'.pointsOver c' i e (cutOrders (C.s i) C.η l) d)
    (hx₀ : x₀ ∈ S.pointsOver c (i.stepBack l) e (cutOrders 0 C.η l₀) d₀)
    (hx₀' : x₀' ∈ S'.pointsOver c' (i.stepBack l) e (cutOrders 0 C.η l₀) d₀) :
    h.HasStop c c' i C.κ H H C.η l x₀ x x₀' x' := by
  -- The side with the negative far window at the pivot leads; by symmetry one lemma serves both.
  obtain hε | hε := Int.units_eq_one_or (C.ε (i.stepBack t))
  · obtain ⟨q, hq, h_rule⟩ := exists_mem_pointsOver_ruleBound_le_of_isLongGap (R' := S') (l₀ := l₀)
      C hU hH hl h_cut h_gap (neg_inj.2 hε) (by simpa only [neg_neg] using hU')
      (by simpa only [ne_eq, neg_inj] using h_gap.sign_ne_or_far_le) c
    exact .inl ⟨q, mem_stopPoints_of_mem_pointsOver hq, h.isSafeMoveSnd_of_killsCokernel h_kill
      (sub_mem_kerWithOrders_of_pointsOver hx' (phi_pow_smul_mem_pointsOver hx₀')) hq
      fun a u hu v _ ↦ h_rule a u hu v⟩
  · obtain ⟨q', hq', h_rule⟩ := exists_mem_pointsOver_ruleBound_le_of_isLongGap (R' := S) (l₀ := l₀)
      C hU' hH hl h_cut h_gap hε hU h_gap.sign_ne_or_far_le c'
    exact .inr ⟨q', mem_stopPoints_of_mem_pointsOver hq', h.isSafeMoveFst_of_killsCokernel h_kill
      (sub_mem_kerWithOrders_of_pointsOver hx (phi_pow_smul_mem_pointsOver hx₀)) hq'
      fun a u hu v _ ↦ h_rule a u hu v⟩

/-- Let the paired sides have their jumps at each letter `j` in `[-η, η]` and in opposite far
windows `∓ε j • [β j, β j + V]`. Let `i` be a plain cut: `0 < l`, and the `l` letters after
`i.stepBack l` share the sign `ρ`, up to far windows that end at or below `η`. Let `x`, `x'` at `i`
and `x₀`, `x₀'` at `i.stepBack l` be points of the two sides over `p ^ e c`, `p ^ e c'` with orders
`-u` on each jump `u`, lowered by `η` at the distinguished element `E` (level `0`). Let `x`, `x'`
have the depth `plainDepth s η l η`: `-u`, raised by `s` at the level `0` and by `η` at the levels
up to `l`. Let `p ^ κ * E ^ s` kill the cokernel at `i` of the Tate dual side, with lattice
`Hom(Y ⊗ Y', O(1))`. Then one side has a stop, at which it rests while the other side moves from
`φ ^ l` of its point at `i.stepBack l` to its point at `i`, safely: `p ^ κ` times the pairing of
this move with all `g • q - q` (`q` the stop) lies in the image of `W(𝔪^♭)`. -/
lemma SidePairing.exists_stop_of_hasSignBefore (C : k.CutScheme) {e : ℕ} (h : S.SidePairing S')
    (hU : ∀ i : k.Letter, FitsWindows C.η (-C.ε i) (C.β i) C.V (S.jumpSet i))
    (hU' : ∀ i : k.Letter, FitsWindows C.η (C.ε i) (C.β i) C.V (S'.jumpSet i)) {i : k.Letter}
    {l s : ℕ} {ρ : ℤˣ} (hl : 0 < l) (h_kill : h.tateDualSide.KillsCokernel i C.κ s)
    (h_plain : C.HasSignBefore i l ρ) {c : S.paramLattice} {c' : S'.paramLattice}
    {d₀ : ℕ → ℤ → ℤ} {x₀ x : S.extensionLattice.Ambient} {x₀' x' : S'.extensionLattice.Ambient}
    (hx : x ∈ S.pointsOver c i e (raisedOrdersAtZero (-C.η)) (plainDepth s C.η l C.η))
    (hx' : x' ∈ S'.pointsOver c' i e (raisedOrdersAtZero (-C.η)) (plainDepth s C.η l C.η))
    (hx₀ : x₀ ∈ S.pointsOver c (i.stepBack l) e (raisedOrdersAtZero (-C.η)) d₀)
    (hx₀' : x₀' ∈ S'.pointsOver c' (i.stepBack l) e (raisedOrdersAtZero (-C.η)) d₀) :
    h.HasStop c c' i C.κ e e C.η l x₀ x x₀' x' :=
  (C.toOpposite h hU hU').hasStop_of_sign hl h_kill h_plain hx hx' hx₀ hx₀'

/-- The scheme of cuts, a chosen set of letters. Let paired sides have their jumps in the low window
`[-η, η]` and in opposite far windows `∓ε i • [β i, β i + V]`. Suppose that `η ≥ 1`, `V + 4 η ≤ W`,
that the shifts have `s i + W ≤ p n`, and that `CutScheme` size conditions hold: `2 b` bounds all
`β i + s i + W`, `n` bounds `G / (p - 1)`, `s₀` bounds `(β i + W) / (p - 3)` for `p ≥ 5`, and `κ` is
large against the cost `X` of one of `J + 1` levels and the cost `δ` of the depth `2 b`. Let each
cut `i` be of a kind at which the cokernel is killed (`IsKillingCut`): `s i = 0` and `β + W ≤ G` at
the next `J` letters, or the chart is unramified, `p ≥ 5` and `s₀ - κ ≤ s i < β i`. Let every letter
have a cut at most `2 J + 1` steps back. Suppose also that the letters after the nearest cut share
the sign of some `i.stepBack t`, up to small far windows, or have a long gap with pivot
`i.stepBack t`. Then, for every `e ≥ 13 κ` and `c`, `c'` in the lattices `paramLattice` of the
sides, the cup product of the cocycles of `c` and `p ^ e c'` is a coboundary. -/
lemma SidePairing.isScaledCupCoboundary_of_cut_windows (C : k.CutScheme) {cut : k.Letter → Prop}
    {e : ℕ} (h : S.SidePairing S')
    (hU : ∀ i : k.Letter, FitsWindows C.η (-C.ε i) (C.β i) C.V (S.jumpSet i))
    (hU' : ∀ i : k.Letter, FitsWindows C.η (C.ε i) (C.β i) C.V (S'.jumpSet i))
    (h_killing : ∀ i : k.Letter, cut i → C.IsKillingCut i)
    (h_cut_before : ∀ i : k.Letter, ∃ l ∈ Set.Ioc 0 (2 * C.J + 1), cut (i.stepBack l))
    (h_gap : ∀ (i : k.Letter) (l : ℕ), i.IsNearestCut cut l → ∃ t : ℕ,
      C.HasSignBefore i l (C.ε (i.stepBack t)) ∨ C.IsLongGap i l t)
    (he : 13 * C.κ ≤ e) (c : S.paramLattice) (c' : S'.paramLattice) :
    h.IsScaledCupCoboundary e c c' := by
  -- Apply the walk. At each cut both sides get a standard point over `p ^ (6 κ)`. The side whose
  -- far window at the pivot is negative leads; its stop is its own point at a plain cut, and comes
  -- from the long gap at the other cuts.
  -- The letter `i.stepBack (l i)` is the nearest cut before `i`.
  choose l hl_le hl_nearest using (fun i : k.Letter ↦ by
    classical
    obtain ⟨⟨h_pos, h_le⟩, h_cut⟩ := Nat.find_spec (h_cut_before i)
    exact ⟨Nat.find (h_cut_before i), h_le, h_pos, h_cut, fun a ⟨ha_pos, ha_lt⟩ ha_cut ↦
      Nat.find_min (h_cut_before i) ha_lt ⟨⟨ha_pos, ha_lt.le.trans h_le⟩, ha_cut⟩⟩
    : ∀ i : k.Letter, ∃ l : ℕ, l ≤ 2 * C.J + 1 ∧ i.IsNearestCut cut l)
  have h_kill (i : k.Letter) (hi : cut i) : h.tateDualSide.KillsCokernel i C.κ (C.s i) :=
    killsCokernel_of_isKillingCut C (fun j _ hw ↦ by
      have h_near := tateDualSide_jump_near h (hU j) (hU' j) hw
      simp only [abs_eq_max_neg] at h_near; have := C.hW; omega) (h_killing i hi)
  -- The standard points of a side `R`; they also have the depth that a plain cut asks.
  have h_points {R : PairingSide O} {σ : k.Letter → ℤˣ}
      (hR : ∀ i : k.Letter, FitsWindows C.η (σ i) (C.β i) C.V (R.jumpSet i)) (d : R.paramLattice) :
      ∃ x : k.Letter → R.extensionLattice.Ambient,
        (∀ i, cut i → x i ∈ R.pointsOver d i (6 * C.κ) (cutOrders (C.s i) C.η (l i))
          (standardDepth (C.s i) C.η (l i + 1))) ∧
        ∀ i, cut i → x i ∈ R.pointsOver d i (6 * C.κ) (raisedOrdersAtZero (-C.η))
          (plainDepth (C.s i) C.η (l i) C.η) := by
    choose! x hx using fun i hi ↦
      pointsOver_cutOrders_nonempty C hR le_rfl (h_killing i hi) (hl_le i) d
    exact ⟨x, hx, fun i hi ↦ mem_pointsOver_plainDepth_of_cutOrders C (hR i) (h_killing i hi)
      (hx i hi)⟩
  obtain ⟨x, hx, hx_plain⟩ := h_points hU c
  obtain ⟨x', hx', hx'_plain⟩ := h_points hU' c'
  refine h.isScaledCupCoboundary_of_stops cut l C.s x x'
    (fun i ↦ ⟨⟨(hl_nearest i).pos, (hl_nearest i).cut_stepBack⟩, fun a ⟨ha_pos, ha_cut⟩ ↦
      le_of_not_gt fun ha_lt ↦ (hl_nearest i).not_cut a ⟨ha_pos, ha_lt⟩ ha_cut⟩)
    h_kill (fun i hi ↦ mem_standardPoints_of_plainDepth (hx_plain i hi))
    (fun i hi ↦ mem_standardPoints_of_plainDepth (hx'_plain i hi)) (fun i hi ↦ ?_) (by omega)
  have h_before : cut (i.stepBack (l i)) := (hl_nearest i).cut_stepBack
  obtain ⟨t, h_plain | h_long⟩ := h_gap i (l i) (hl_nearest i)
  · exact h.exists_stop_of_hasSignBefore C hU hU' (hl_nearest i).pos (h_kill i hi) h_plain
      (hx_plain i hi) (hx'_plain i hi) (hx_plain _ h_before) (hx'_plain _ h_before)
  · -- The cut before a long gap has shift `0`.
    exact h.exists_stop_of_isLongGap C hU hU' le_rfl (hl_le i) (h_killing _ h_before)
      (h_long.shift_eq_zero ▸ h_kill _ h_before) h_long (hx i hi) (hx' i hi)
      (h_long.shift_eq_zero ▸ hx _ h_before) (h_long.shift_eq_zero ▸ hx' _ h_before)

/-- The scheme of cuts with all shifts `0`, for far windows of width `V` starting at `β i ≤ max b W`
at each letter `i` with signs `ε i`, low-window radius `η ≥ 1`, and padded width `W ≥ V + 4 η`.
Let `8 e ≤ p ^ (J + 1)`, `2 e (b + W) ≤ p ^ (J + 1) δ` and
`4 (J + 1 + d) W + ⌊log_p (2 (b + W))⌋ ≤ X`. Then a `CutScheme` holds with
`κ = 12 ((J + 1) X + δ) + 1`, `b + W` in place of `b`, `n = G = 2 W`,
`s₀ = ⌊(b + 2 W) / (p - 3)⌋ + 1`, and `ω = η`. -/
def _root_.New.Lift.KummerChart.cutScheme_zero_shift {β : k.Letter → ℕ} {ε : k.Letter → ℤˣ}
    {η V W X δ b J : ℕ} (hη : 1 ≤ η) (hW : V + 4 * η ≤ W)
    (hβ_le : ∀ i : k.Letter, β i ≤ max b W) (h_ram : 8 * k.e ≤ p ^ (J + 1))
    (h_depth : k.e * (2 * (b + W)) ≤ p ^ (J + 1) * δ)
    (hX : 4 * (J + 1 + k.differentBound) * W + p.log (2 * (b + W)) ≤ X) : k.CutScheme :=
  ⟨fun _ ↦ 0, β, ε, η, V, W, X, δ, 12 * ((J + 1) * X + δ) + 1, b + W, 2 * W, J,
    (b + 2 * W) / (p - 3) + 1, 2 * W, η, hη, hW,
    fun _ ↦ by nlinarith [(Fact.out : p.Prime).two_le], by lia, Nat.lt_succ_self _, h_depth, h_ram,
    fun i ↦ by grw [hβ_le i]; omega,
    Nat.le_mul_of_pos_left _ (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt),
    fun hp i ↦ ((by grw [hβ_le i]; omega : β i + W ≤ b + 2 * W).trans
      (Nat.lt_mul_div_succ _ (by omega)).le)⟩

/-- On an unramified chart the ramification index `k.e` is `1`, so `8 e ≤ p ^ 2` if `p ≥ 3`. -/
lemma _root_.New.Lift.KummerChart.IsUnramified.eight_mul_e_le_sq (hk : k.IsUnramified)
    (hp : 3 ≤ p) : 8 * k.e ≤ p ^ 2 :=
  (by simp [hk.right.1] : 8 * k.e ≤ 3 ^ 2).trans (pow_le_pow_left' hp 2)

/-- Let the far windows `± [β i, β i + V]` start at `b` at the b-letters, or thick letters (those
with `T`), and at `G` at the others, the thin ones, where `η ≥ 1` and `G + V ≤ η`. Among the letters
`i.stepBack r` with `r < l`, let only those with `r = 0` or `r + (J + 1) = l` be possibly thick. Let
the chart be unramified with `p ≥ 7` and `10 p ^ J η ≤ b`, or let the sign `ε` be constant. Then for
some pivot `i.stepBack t` these `l` letters have the sign of the pivot or a far window that ends at
or below `η` (`HasSignBefore`), or there is a long gap among them: the pivot is `J + 1` steps after
`i.stepBack l`, its window starts beyond `s₀ + ω (1 + ⋯ + p ^ J)` and the others have the opposite
sign or small windows (`IsLongGap` with all shifts `0`, `s₀ = ⌊(b + 10 η) / (p - 3)⌋ + 1` and
`ω = η`). -/
lemma _root_.New.Lift.KummerChart.CutScheme.hasSignBefore_or_isLongGap (C : k.CutScheme)
    {T : k.Letter → Prop} {b G : ℕ} {i : k.Letter} {l : ℕ}
    (hs_zero : ∀ j : k.Letter, C.s j = 0) (hs₀ : C.s₀ = (b + 10 * C.η) / (p - 3) + 1)
    (hω : C.ω = C.η)
    (hβ_thick : ∀ j : k.Letter, T j → C.β j = b) (hβ_thin : ∀ j : k.Letter, ¬T j → C.β j = G)
    (hG : G + C.V ≤ C.η)
    (h_unramified_or_constSign :
      k.IsUnramified ∧ 7 ≤ p ∧ 10 * p ^ C.J * C.η ≤ b ∨ ∀ j j' : k.Letter, C.ε j = C.ε j')
    (h_thick_positions : ∀ r : ℕ, r < l → T (i.stepBack r) → r = 0 ∨ r + (C.J + 1) = l) :
    ∃ t : ℕ, C.HasSignBefore i l (C.ε (i.stepBack t)) ∨ C.IsLongGap i l t := by
  by_cases h_sign : C.HasSignBefore i l (C.ε (i.stepBack 0))
  · exact ⟨0, .inl h_sign⟩
  -- The pivot `i.stepBack t` is a b-letter and its sign is not that of `i`; so `t + (J + 1) = l`.
  obtain ⟨t, ht_lt, ht_sign, ht_far⟩ :
      ∃ t < l, C.ε (i.stepBack t) ≠ C.ε (i.stepBack 0) ∧ C.η < C.β (i.stepBack t) + C.V := by
    simpa only [CutScheme.HasSignBefore, not_forall, not_or, not_le, exists_prop] using h_sign
  obtain ⟨hk, hp, hb⟩ :=
    h_unramified_or_constSign.resolve_right fun h_const ↦ ht_sign (h_const _ _)
  have ht_thick : T (i.stepBack t) := by grind
  have h_pivot : t + (C.J + 1) = l :=
    (h_thick_positions t ht_lt ht_thick).resolve_left fun ht_zero ↦ ht_sign (by rw [ht_zero])
  -- The letters other than `i` and the pivot are thin, so their far windows are small.
  have h_small (a : ℕ) (ha : a < l) (ha_ne : a ≠ t) (ha_pos : a ≠ 0) :
      C.β (i.stepBack a) + C.V ≤ C.η := by
    rwa [hβ_thin _ fun h_thick ↦ (h_thick_positions a ha h_thick).elim ha_pos (by omega)]
  -- The geometric sum is at most `2 p ^ J`, and `(b + 10 η) / 4 + 1 + 2 p ^ J η < b`.
  have h_lt_pivot : (b + 10 * C.η) / (p - 3) + 1 + C.η * ∑ a ∈ range (C.J + 1), p ^ a < b := by
    have h_sum : ∑ a ∈ range (C.J + 1), p ^ a ≤ 2 * p ^ C.J := by
      rw [sum_range_succ, two_mul, add_le_add_iff_right]
      exact (Nat.geomSum_lt (by omega) (by simp)).le
    have h_div : (b + 10 * C.η) / (p - 3) ≤ (b + 10 * C.η) / 4 :=
      Nat.div_le_div_left (by omega) four_pos
    have hη_le : C.η ≤ p ^ C.J * C.η := Nat.le_mul_of_pos_left C.η (by positivity)
    have := C.hη
    calc _ ≤ (b + 10 * C.η) / 4 + 1 + C.η * (2 * p ^ C.J) := by gcongr
      _ < b := by lia
  exact ⟨t, .inr ⟨hk, by omega, hs_zero _, h_pivot,
    by rw [hs₀, hω, hβ_thick _ ht_thick]; exact h_lt_pivot,
    fun a ha ha_ne ↦ (eq_or_ne a 0).elim (fun h0 ↦ .inl (h0 ▸ ht_sign.symm))
      fun h0 ↦ .inr (h_small a ha ha_ne h0),
    hω.ge, fun a ha ha_gt ↦ hω ▸ h_small a ha ha_gt.ne' (by omega)⟩⟩

/-- Suppose that no three letters with `T` follow one another with both gaps between `1` and `J`.
Then one of the `2 J + 1` letters before `i` is followed by `J` letters without `T`. -/
lemma _root_.New.Lift.KummerChart.Letter.exists_hasThinSuccessors_stepBack {T : k.Letter → Prop}
    {J : ℕ} (h_sparse : ∀ i : k.Letter, ∀ s ∈ Icc 1 J, ∀ t ∈ Icc 1 J,
      T i → T ((k.letterFrob ^ s) i) → ¬T ((k.letterFrob ^ (s + t)) i)) (i : k.Letter) :
    ∃ l ∈ Set.Ioc 0 (2 * J + 1), (i.stepBack l).HasThinSuccessors T J := by
  -- If the letter `J + 1` steps back fails, then a letter `r` steps back has `T`, with `1 ≤ r ≤ J`.
  -- That letter or the one `J + 1` steps before it has the property.
  by_cases h_first : (i.stepBack (J + 1)).HasThinSuccessors T J
  · exact ⟨J + 1, ⟨J.succ_pos, by omega⟩, h_first⟩
  obtain ⟨n, hn_pos, hn_le, h_next⟩ :
      ∃ n : ℕ, n ≥ 1 ∧ n ≤ J ∧ T ((k.letterFrob ^ n) (i.stepBack (J + 1))) := by
    simpa only [Letter.HasThinSuccessors, not_forall, not_not, exists_prop] using h_first
  have h_thick : T (i.stepBack (J + 1 - n)) := by simpa [pow_sub _ hn_le.step] using h_next
  by_cases h_second : (i.stepBack (J + 1 - n)).HasThinSuccessors T J
  · exact ⟨J + 1 - n, by grind, h_second⟩
  · exact ⟨J + 1 - n + (J + 1), by grind,
      Letter.hasThinSuccessors_stepBack_add h_sparse i _ h_second h_thick⟩

/-- Suppose that no three letters with `T` follow one another with both gaps between `1` and `J`.
Let `i.stepBack l` be the nearest letter before `i` that is followed by `J` letters without `T`.
Then a letter `i.stepBack r` with `T` and `r < l` is `i` itself or lies `J + 1` steps after
`i.stepBack l`. -/
lemma _root_.New.Lift.KummerChart.Letter.IsNearestCut.eq_zero_or_add_eq_of_hasThinSuccessors
    {T : k.Letter → Prop} {J l r : ℕ} {i : k.Letter}
    (h_nearest : i.IsNearestCut (fun i' : k.Letter ↦ i'.HasThinSuccessors T J) l)
    (h_sparse : ∀ i : k.Letter, ∀ s ∈ Icc 1 J, ∀ t ∈ Icc 1 J,
      T i → T ((k.letterFrob ^ s) i) → ¬T ((k.letterFrob ^ (s + t)) i))
    (hr : r < l) (h_thick : T (i.stepBack r)) : r = 0 ∨ r + (J + 1) = l := by
  refine r.eq_zero_or_pos.imp_right fun hr_pos ↦ le_antisymm ?_ ?_
  · -- The letter with `T` is not among the `J` letters after `i.stepBack l`.
    by_contra h_near
    exact h_nearest.cut_stepBack (l - r) (by omega) (by omega)
      (by simpa [← pow_mul_pow_sub _ hr.le] using h_thick)
  · -- Otherwise the letter `r + (J + 1)` steps back would be a nearer cut.
    by_contra h_far
    exact h_nearest.not_cut (r + (J + 1)) (by grind)
      (Letter.hasThinSuccessors_stepBack_add h_sparse i r
        (h_nearest.not_cut r ⟨hr_pos, hr⟩) h_thick)

/-- Sparse b-letters. Let the sides `S`, `S'` of a Kummer chart be paired by `h`; each side has
lattices Y and `C = paramLattice`, a map `cocycleMap` from C to the crystalline cocycles of Y, and a
finite set of jumps at each letter. The b-letters, or thick letters, are those with `T i`. At each
b-letter `i`, let each jump of `S` lie in `[-η, η]` or in the far window `-ε i [b, b + V]`, and each
jump of `S'` in `[-η, η]` or in `ε i [b, b + V]`. At the other letters `G` replaces `b`. Here
`η ≥ 1` and `G + V ≤ η`. Suppose that no three b-letters follow one another under Frobenius with
both gaps between `1` and `J ≥ 1`. Suppose also that the chart is unramified with `p ≥ 7` and
`10 p ^ J η ≤ b`, or that the sign `ε` is constant and `8 e ≤ p ^ (J + 1)`. Let
`2 e (b + 5 η) ≤ p ^ (J + 1) δ` and `20 (J + 1 + d) η + ⌊log_p (2 (b + 5 η))⌋ ≤ X`. Here `e = k.e`
is the ramification index, and `d = k.differentBound` is `0` if `e = 1` and `v_p(e) + 1` otherwise.
Then for `c` in `S.paramLattice` and `c'` in `S'.paramLattice`, the cup product of the cocycles
`S.cocycleMap c` and `p ^ (10³ (δ + (J + 1) X)) • S'.cocycleMap c'` is a coboundary
(`IsScaledCupCoboundary`). -/
lemma SidePairing.isScaledCupCoboundary_sparse_thick {T : k.Letter → Prop} [DecidablePred T]
    {ε : k.Letter → ℤˣ} {η V X δ b J G : ℕ} (h : S.SidePairing S') (hη : 1 ≤ η)
    (hU : ∀ i : k.Letter, FitsWindows η (-ε i) (if T i then b else G) V (S.jumpSet i))
    (hU' : ∀ i : k.Letter, FitsWindows η (ε i) (if T i then b else G) V (S'.jumpSet i))
    (hG : G + V ≤ η) (hJ : 1 ≤ J) (h_sparse : ∀ i : k.Letter, ∀ s ∈ Icc 1 J, ∀ t ∈ Icc 1 J,
      T i → T ((k.letterFrob ^ s) i) → ¬T ((k.letterFrob ^ (s + t)) i))
    (h_unramified_or_constSign : k.IsUnramified ∧ 7 ≤ p ∧ 10 * p ^ J * η ≤ b ∨
      (∀ i i' : k.Letter, ε i = ε i') ∧ 8 * k.e ≤ p ^ (J + 1))
    (h_depth : k.e * (2 * (b + 5 * η)) ≤ p ^ (J + 1) * δ)
    (hX : 20 * (J + 1 + k.differentBound) * η + p.log (2 * (b + 5 * η)) ≤ X)
    (c : S.paramLattice) (c' : S'.paramLattice) :
    h.IsScaledCupCoboundary (10 ^ 3 * (δ + (J + 1) * X)) c c' := by
  -- Apply `isScaledCupCoboundary_of_cut_windows` without shifts, cutting at the letters that are
  -- followed by `J` thin letters, with the width `W = 5 η` and the least `κ` it allows.
  have h_ram : 8 * k.e ≤ p ^ (J + 1) := h_unramified_or_constSign.elim
    (fun ⟨hk, hp, _⟩ ↦ (hk.eight_mul_e_le_sq (by omega)).trans
      (Nat.pow_le_pow_right (by omega) (by omega)))
    And.right
  let C : k.CutScheme := cutScheme_zero_shift (β := fun i ↦ if T i then b else G) (ε := ε)
    hη (by omega : V + 4 * η ≤ 5 * η) (fun _ ↦ by grind) h_ram h_depth (by linarith)
  refine h.isScaledCupCoboundary_of_cut_windows C hU hU'
    (fun i (hi : i.HasThinSuccessors T J) ↦ .of_thin rfl fun t ht ↦ by
      obtain ⟨ht_pos, ht_le⟩ := mem_Icc.1 ht
      simp only [C, cutScheme_zero_shift, ite_eq_right (hi t ht_pos ht_le)]; omega)
    (Letter.exists_hasThinSuccessors_stepBack h_sparse)
    (fun i l h_nearest ↦ C.hasSignBefore_or_isLongGap (fun _ ↦ rfl)
      (by simp only [C, cutScheme_zero_shift]; congr 2; omega) rfl (fun _ h ↦ ite_eq_left h)
      (fun _ h ↦ ite_eq_right h) hG (h_unramified_or_constSign.imp_right And.left)
      fun _ ↦ h_nearest.eq_zero_or_add_eq_of_hasThinSuccessors h_sparse)
    (by simp only [C, cutScheme_zero_shift]; lia) c c'

/-- The scheme of cuts with `J = 1`, on an unramified chart with `p ≥ 7`. Here `β i` is the start
of the far window of the jumps at the letter `i` and `s i` its shift, the pole order at `E` allowed
if `i` is a cut; let `β i ≤ b` and `s i ≤ ⌊b / p⌋ - 7 K`. Let `b < K p ^ 2`, `2 G < K p` and
`V + 4 η ≤ W ≤ K`. Then a `CutScheme` holds with `X = 3 K + ⌊log_p (2 (b + W))⌋`, `δ = 4 K`,
`κ = 12 (2 X + δ) + 1`, `n = K`, `s₀ = ⌊b / p⌋ + 12 K`, `ω = G + W`, and `b + W`, `G + W` in place
of `b`, `G`. -/
def _root_.New.Lift.KummerChart.cutScheme_of_isUnramified {s β : k.Letter → ℕ}
    {ε : k.Letter → ℤˣ} {η V W b G K : ℕ} (hk : k.IsUnramified) (hp : 7 ≤ p)
    (hη : 1 ≤ η) (hW : V + 4 * η ≤ W)
    (hβ_le : ∀ i : k.Letter, β i ≤ b) (hs_le : ∀ i : k.Letter, s i ≤ b / p - 7 * K)
    (hbK : b < K * p ^ 2) (hGK : 2 * G < K * p) (hWK : W ≤ K) : k.CutScheme :=
  ⟨s, β, ε, η, V, W, 3 * K + p.log (2 * (b + W)), 4 * K,
    12 * (2 * (3 * K + p.log (2 * (b + W))) + 4 * K) + 1, b + W, K, 1, b / p + 12 * K, G + W,
    G + W, hη, hW,
    fun i ↦ by
      have : 7 * K ≤ p * K := Nat.mul_le_mul_right K hp
      have : b / p < p * K := Nat.div_lt_of_lt_mul (by lia)
      have := hs_le i; omega,
    by rw [hk.2.2]; omega, by omega,
    by have : K ≤ K * p ^ 2 := Nat.le_mul_of_pos_right K (by positivity)
       rw [hk.2.1, one_mul]; lia,
    hk.eight_mul_e_le_sq (by omega),
    fun i ↦ by have := hβ_le i; have := hs_le i; have := b.div_le_self p; omega,
    by have : K * 7 ≤ K * p := mul_le_mul_right hp K
       rw [Nat.sub_one_mul, mul_comm p K]; omega,
    fun _ i ↦ by
      -- `b - (p - 3) (b / p) < 3 (b / p) + p ≤ 4 p K`
      have h_lt_div : b < b / p * p + p := b.lt_div_mul_add (by omega)
      have h_div_lt : b / p < K * p := Nat.div_lt_of_lt_mul (by lia)
      have hpK : p ≤ K * p :=
        Nat.le_mul_of_pos_left p (Nat.pos_of_mul_pos_right (Nat.zero_lt_of_lt hGK))
      have hK_seven : K * 7 ≤ K * p := mul_le_mul_right hp K
      have h_expand : (p - 3) * (b / p + 12 * K) + 3 * (b / p + 12 * K) =
          b / p * p + 12 * (K * p) := by
        rw [← add_mul, Nat.sub_add_cancel (by omega)]; ring
      grw [hβ_le i]; omega⟩

/-- Suppose `cut` holds at every letter `i` with `T i` and at every letter `i` with
`¬T (k.letterFrob i)`, where `k.letterFrob` sends a letter `x` to `x ^ p`. Then `cut (i.stepBack 1)`
or `cut (i.stepBack 2)` holds, that is, `cut` holds at one of the two letters before `i`. -/
lemma _root_.New.Lift.KummerChart.Letter.cut_stepBack_one_or_two {cut T : k.Letter → Prop}
    (h_cut_thick : ∀ i : k.Letter, T i → cut i)
    (h_cut_thin : ∀ i : k.Letter, ¬T (k.letterFrob i) → cut i) (i : k.Letter) :
    cut (i.stepBack 1) ∨ cut (i.stepBack 2) := by
  by_cases h_thick : T (i.stepBack 1)
  · exact .inl (h_cut_thick _ h_thick)
  · exact .inr (h_cut_thin _ (by simpa [pow_succ] using h_thick))

/-- On an unramified chart with `p ≥ 7`, let the far windows start at `b` at the b-letters (those
with `T`) and at `G` at the others, the thin ones. Let the shifts be at most `⌊b / p⌋ - 7 K`, and
`0` at the letters with a thin successor, where `0 < G`, `b < K p ^ 2` and `V + 4 η ≤ W ≤ K`. The
cuts are the letters whose shift is less than the start of their far window; let the b-letters and
the letters with a thin successor be cuts. If `i.stepBack l` is the nearest cut before `i`, then
each of the `l` letters after it has the sign of `i` or a far window that ends at or below `η`
(`HasSignBefore`), or there is a long gap with pivot `i` (pivot index `0`): its window starts beyond
`s₀ + ω (1 + p)`, for `s₀ = ⌊b / p⌋ + 12 K` and `ω = G + W`, and the letter before has the opposite
sign. -/
lemma _root_.New.Lift.KummerChart.CutScheme.hasSignBefore_or_isLongGap_of_two_sizes
    (C : k.CutScheme) {T : k.Letter → Prop} {b G K : ℕ} {i : k.Letter} {l : ℕ}
    (h_nearest : i.IsNearestCut (fun i' : k.Letter ↦ C.s i' < C.β i') l)
    (hk : k.IsUnramified) (hp : 7 ≤ p) (hJ : C.J = 1) (hs₀ : C.s₀ = b / p + 12 * K)
    (hω : C.ω = G + C.W) (hβ_thick : ∀ j : k.Letter, T j → C.β j = b)
    (hβ_thin : ∀ j : k.Letter, ¬T j → C.β j = G)
    (hs_le : ∀ j : k.Letter, C.s j ≤ b / p - 7 * K)
    (hs_thin_succ : ∀ j : k.Letter, ¬T (k.letterFrob j) → C.s j = 0)
    (h_cut_thick : ∀ j : k.Letter, T j → C.s j < C.β j)
    (h_cut_thin_succ : ∀ j : k.Letter, ¬T (k.letterFrob j) → C.s j < C.β j)
    (hG_pos : 0 < G) (hbK : b < K * p ^ 2) (hWK : C.W ≤ K) :
    C.HasSignBefore i l (C.ε (i.stepBack 0)) ∨ C.IsLongGap i l 0 := by
  have hl_le : l ≤ 2 := by
    by_contra hl_gt
    obtain h_cut | h_cut := i.cut_stepBack_one_or_two h_cut_thick h_cut_thin_succ <;>
      exact h_nearest.not_cut _ (by grind) h_cut
  by_cases h_opposite : l = 2 ∧ C.ε (i.stepBack 1) ≠ C.ε (i.stepBack 0)
  · -- The letter before `i` is not a cut, so it is not a b-letter and `i` is a b-letter.
    obtain ⟨rfl, h_sign⟩ := h_opposite
    have h_not_cut : ¬C.s (i.stepBack 1) < C.β (i.stepBack 1) := h_nearest.not_cut 1 (by simp)
    have h_prev_thin : ¬T (i.stepBack 1) := mt (h_cut_thick _) h_not_cut
    have h_thick : T i := by_contra fun h_thin ↦
      h_not_cut (h_cut_thin_succ _ (by simpa [pow_succ] using h_thin))
    -- As that letter is not a cut, `0 < G ≤ s (i.stepBack 1) ≤ b / p - 7 K`.
    have hβ_prev : C.β (i.stepBack 1) = G := hβ_thin _ h_prev_thin
    have hG_le : G + 7 * K ≤ b / p := by have := hs_le (i.stepBack 1); omega
    have h_lt_pivot : b / p + 12 * K + (G + C.W) * (1 + p) < b := by
      have := b.div_mul_le_self p
      have := Nat.div_lt_of_lt_mul (by lia : b < p * (K * p))
      have := Nat.mul_le_mul_right (1 + p) (by omega : G + C.W + 6 * K ≤ b / p)
      lia
    exact .inr ⟨hk, by omega, hs_thin_succ _ (by simpa [pow_succ] using h_prev_thin), by omega,
      by simpa [hJ, hs₀, hω, sum_range_succ, hβ_thick i h_thick] using h_lt_pivot,
      fun a ha ha_ne ↦ .inl (by rwa [show a = 1 by omega]), by have := C.hW; omega,
      fun a ha ha_pos ↦ by rw [hω, show a = 1 by omega, hβ_prev]; have := C.hW; omega⟩
  · refine .inl fun r hr ↦ .inl ?_
    obtain rfl | rfl : r = 0 ∨ r = 1 := by omega
    exacts [rfl, by_contra fun h_sign ↦ h_opposite ⟨by omega, h_sign⟩]

/-- Let the Kummer chart `k` over `Γ` be unramified, and let the fixed prime `p` be at least `7`.
Let the sides `S`, `S'`, paired by `h`, have their jumps at each letter `i` in `[-η, η]` and in
opposite far windows of signs `∓ε i` and width `V`, which start at `b` at the b-letters (those with
`T i`) and at `G` at the others, where `0 < G ≤ b`, `η ≥ 1` and `V + 4 η ≤ W`. If `b < K p ^ 2`,
`2 G < K p` and `W ≤ K`, then the cup product of the cocycles `S.cocycleMap c` and `p ^ (10⁴
(K + ⌊log_p (2 (b + W))⌋)) • S'.cocycleMap c'` is a coboundary. -/
lemma SidePairing.isScaledCupCoboundary_any_pattern {T : k.Letter → Prop} [DecidablePred T]
    {ε : k.Letter → ℤˣ} {η V W b G K : ℕ} (h : S.SidePairing S') (hη : 1 ≤ η) (hW : V + 4 * η ≤ W)
    (hU : ∀ i : k.Letter, FitsWindows η (-ε i) (if T i then b else G) V (S.jumpSet i))
    (hU' : ∀ i : k.Letter, FitsWindows η (ε i) (if T i then b else G) V (S'.jumpSet i))
    (hk : k.IsUnramified) (hp : 7 ≤ p) (hG_pos : 0 < G) (hGb : G ≤ b) (hbK : b < K * p ^ 2)
    (hGK : 2 * G < K * p) (hWK : W ≤ K) (c : S.paramLattice) (c' : S'.paramLattice) :
    h.IsScaledCupCoboundary (10 ^ 4 * (K + p.log (2 * (b + W)))) c c' := by
  -- Apply `isScaledCupCoboundary_of_cut_windows` with `J = 1`. A letter whose successor is a
  -- b-letter has shift `b / p - 7 K`, the others have shift `0`; the cuts are the letters with
  -- `s i < β i`.
  let C : k.CutScheme := cutScheme_of_isUnramified (β := fun i ↦ if T i then b else G)
    (s := fun i ↦ if T (k.letterFrob i) then b / p - 7 * K else 0) (ε := ε)
    hk hp hη hW (fun _ ↦ by grind) (fun _ ↦ by grind) hbK hGK hWK
  have hs_le (i : k.Letter) : C.s i ≤ b / p - 7 * K := by
    dsimp [C, cutScheme_of_isUnramified]; grind
  -- A cut with a thin successor has shift `0`; one whose successor is a b-letter has
  -- `s₀ ≤ s i + 19 K`.
  have h_killing (i : k.Letter) (hi : C.s i < C.β i) : C.IsKillingCut i := by
    by_cases h_thick : T (k.letterFrob i)
    · exact .of_isUnramified hi hk (by omega) (by
        simp only [C, cutScheme_of_isUnramified, ite_eq_left h_thick]; omega)
    · exact .of_thin (ite_eq_right h_thick) fun t ht ↦ by
        obtain rfl : t = 1 := by simpa [C, cutScheme_of_isUnramified] using ht
        simp [C, cutScheme_of_isUnramified, ite_eq_right h_thick]
  -- Thick letters are cuts, and so are the letters with a thin successor.
  have h_cut_thick (i : k.Letter) (hi : T i) : C.s i < C.β i :=
    ((hs_le i).trans (Nat.sub_le _ _)).trans_lt (by
      rw [show C.β i = b from ite_eq_left hi]
      exact Nat.div_lt_self (hG_pos.trans_le hGb) (by omega))
  have h_cut_thin_succ (i : k.Letter) (hi : ¬T (k.letterFrob i)) : C.s i < C.β i := by
    dsimp [C, cutScheme_of_isUnramified]; rw [ite_eq_right hi]; grind
  exact h.isScaledCupCoboundary_of_cut_windows C hU hU' h_killing
    (fun i ↦ (i.cut_stepBack_one_or_two h_cut_thick h_cut_thin_succ).elim
      (⟨1, by simp [C, cutScheme_of_isUnramified], ·⟩)
      (⟨2, by simp [C, cutScheme_of_isUnramified], ·⟩))
    (fun i l h_nearest ↦ ⟨0, C.hasSignBefore_or_isLongGap_of_two_sizes h_nearest hk hp rfl rfl rfl
      (fun _ h ↦ ite_eq_left h) (fun _ h ↦ ite_eq_right h) hs_le (fun _ h ↦ ite_eq_right h)
      h_cut_thick h_cut_thin_succ hG_pos hbK hWK⟩)
    (by simp only [C, cutScheme_of_isUnramified]; lia) c c'

end PairingSide

end SparseThickLetters

end New.Lift.KummerChart
