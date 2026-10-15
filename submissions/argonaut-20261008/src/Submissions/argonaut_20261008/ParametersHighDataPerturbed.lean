import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersHighData
import Submissions.argonaut_20261008.PerturbedBudgetWithSlots

namespace OAI

noncomputable section
open scoped BigOperators

namespace SevenEighths.Parameters

/-!
# Additive perturbed scalar data

This file is additive: it does not modify `HighData`, the official budget
module, or any analytic/high-probe statement.
-/

/-- Fixed perturbation size `ρ = 10⁻⁶`. -/
def perturbedRho : ℝ := 1 / 1000000

/-- Fixed total slot mass `1/6 + ρ`. -/
def perturbedTotalE : ℝ := 1 / 6 + perturbedRho

/-- Fixed perturbed height `13/16 + 3ρ/2`. -/
def perturbedHeight : ℝ := 13 / 16 + 3 * perturbedRho / 2

/-- Boundary parameter, distinct from the positive saving field `sigma`. -/
def perturbedBoundary : ℝ := 7 / 8 - perturbedRho / 4

lemma half_le_perturbedBoundary : (1 / 2 : ℝ) ≤ perturbedBoundary := by
  norm_num [perturbedBoundary, perturbedRho]

/-- Concrete residual scalar budget used by `HighDataPerturbed`. -/
def perturbedBv6 : ℝ := 5861 / 4700160000

lemma perturbedTotalE_pos : 0 < perturbedTotalE := by
  norm_num [perturbedTotalE, perturbedRho]

lemma perturbedTotalE_nonneg : 0 ≤ perturbedTotalE :=
  perturbedTotalE_pos.le

lemma perturbedTotalE_le_one : perturbedTotalE ≤ 1 := by
  norm_num [perturbedTotalE, perturbedRho]

lemma one_sixth_le_perturbedTotalE : (1 / 6 : ℝ) ≤ perturbedTotalE := by
  norm_num [perturbedTotalE, perturbedRho]

lemma perturbedHeight_nonneg : 0 ≤ perturbedHeight := by
  norm_num [perturbedHeight, perturbedRho]

lemma perturbedHeight_le_one : perturbedHeight ≤ 1 := by
  norm_num [perturbedHeight, perturbedRho]

lemma thirteen_sixteenths_le_perturbedHeight :
    (13 / 16 : ℝ) ≤ perturbedHeight := by
  norm_num [perturbedHeight, perturbedRho]

lemma perturbedBv6_pos : 0 < perturbedBv6 := by
  norm_num [perturbedBv6]

lemma perturbed_physical_conductor_cap_of_t_small
    {t : ℝ} (ht : t ≤ 1 / 100000000) :
    perturbedHeight + t + 2 * t ≤ 7 / 8 := by
  norm_num [perturbedHeight, perturbedRho] at ⊢
  linarith

/-!
## Arbitrary-total injective slots

These theorem names are new, so this file can coexist with the official
`ParametersSlotLengths` declarations.  The construction is the affine-weight
construction requested in the packet.
-/

/--
For every positive total mass and positive cap, construct a nonempty finite
injective family of positive slots, each strictly below the cap, whose sum is
exactly the prescribed total mass.
-/
theorem exists_distinct_slot_lengths_total_perturbed
    (Ltotal L : ℝ) (hLtotal : 0 < Ltotal) (hL : 0 < L) :
    ∃ N : ℕ, 0 < N ∧
      ∃ ell : Fin N → ℝ,
        Function.Injective ell ∧
        (∀ j, 0 < ell j ∧ ell j < L) ∧
        (∑ j, ell j) = Ltotal := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2 * Ltotal / L))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNp : 0 < (N : ℝ) := by
    linarith
  have hNnat : 0 < N := by
    exact_mod_cast hNp
  have hNL : 2 * Ltotal / L < (N : ℝ) :=
    (le_max_right _ _).trans_lt hN
  have hsmall : 2 * Ltotal / (N : ℝ) < L := by
    have hcross : 2 * Ltotal < (N : ℝ) * L :=
      (div_lt_iff₀ hL).mp hNL
    apply (div_lt_iff₀ hNp).mpr
    nlinarith

  let w : Fin N → ℝ := fun j => 1 + (j.val : ℝ) / (N : ℝ)
  let A : ℝ := ∑ j, w j

  have hw (j : Fin N) : 1 ≤ w j ∧ w j < 2 := by
    have hj : (j.val : ℝ) < N := by
      exact_mod_cast j.isLt
    have hdiv : (j.val : ℝ) / (N : ℝ) < 1 :=
      (div_lt_one hNp).mpr hj
    dsimp only [w]
    constructor
    · linarith [div_nonneg (Nat.cast_nonneg j.val) hNp.le]
    · linarith

  have hA : (N : ℝ) ≤ A := by
    calc
      (N : ℝ) = ∑ _j : Fin N, (1 : ℝ) := by simp
      _ ≤ ∑ j : Fin N, w j :=
        Finset.sum_le_sum fun j _ => (hw j).1
      _ = A := rfl

  have hAp : 0 < A := hNp.trans_le hA
  let D : ℝ := A / Ltotal
  have hDp : 0 < D := div_pos hAp hLtotal
  have hDne : D ≠ 0 := hDp.ne'
  let ell : Fin N → ℝ := fun j => w j / D

  refine ⟨N, hNnat, ell, ?_, ?_, ?_⟩

  · intro j k heq
    dsimp only [ell] at heq
    have hwjk : w j = w k := (div_left_inj' hDne).mp heq
    have hjk :
        (j.val : ℝ) / (N : ℝ) = (k.val : ℝ) / (N : ℝ) := by
      dsimp [w] at hwjk
      linarith
    have he' : (j.val : ℝ) = (k.val : ℝ) :=
      (div_left_inj' hNp.ne').mp hjk
    apply Fin.ext
    exact_mod_cast he'

  · intro j
    constructor
    · dsimp only [ell]
      exact div_pos (by linarith [(hw j).1]) hDp
    · dsimp only [ell]
      calc
        w j / D < 2 / D :=
          (div_lt_div_iff_of_pos_right hDp).mpr (hw j).2
        _ = 2 * Ltotal / A := by
          dsimp [D]
          field_simp [hAp.ne', hLtotal.ne']
        _ ≤ 2 * Ltotal / (N : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) hNp hA
        _ < L := hsmall

  · dsimp only [ell]
    rw [← Finset.sum_div]
    change A / D = Ltotal
    dsimp [D]
    field_simp [hAp.ne', hLtotal.ne']

/--
Arbitrary-total physical slot construction.  Besides positivity, injectivity,
and the exact sum, it proves both absolute slot bounds and all width bounds
uniformly for every `d ∈ [dmin,dmax]`.
-/
theorem exists_physical_slot_lengths_total_perturbed
    (Ltotal dmin dmax mesh R : ℝ)
    (hLtotal : 0 < Ltotal)
    (hdmin : 0 < dmin)
    (hd : dmin ≤ dmax)
    (hm : 0 < mesh)
    (hR : 0 < R) :
    ∃ N : ℕ, 0 < N ∧
      ∃ ell : Fin N → ℝ,
        ∃ rmin : ℝ,
          0 < rmin ∧
          Function.Injective ell ∧
          (∑ j, ell j) = Ltotal ∧
          (∀ j,
            0 < ell j ∧
            dmax * rmin ≤ ell j ∧
            ell j ≤ dmin * mesh ∧
            ell j ≤ dmin * R) ∧
          (∀ d : ℝ,
            dmin ≤ d →
            d ≤ dmax →
            ∀ j,
              rmin ≤ ell j / d ∧
              ell j / d ≤ mesh ∧
              ell j / d ≤ R) := by
  obtain ⟨N, hN, ell, hi, he, hS⟩ :=
    exists_distinct_slot_lengths_total_perturbed
      Ltotal (dmin * min mesh R) hLtotal
      (mul_pos hdmin (lt_min hm hR))

  have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
    ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  obtain ⟨j, hj, hjmin⟩ :=
    Finset.exists_min_image Finset.univ ell hne

  have hmax : 0 < dmax := hdmin.trans_le hd
  let rmin : ℝ := ell j / (2 * dmax)
  have hr : 0 < rmin := div_pos (he j).1 (by positivity)

  have hlo (k : Fin N) : dmax * rmin ≤ ell k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax * rmin = ell j / 2 := by
      dsimp [rmin]
      field_simp
    rw [hiden]
    linarith [(he j).1]

  have hup (k : Fin N) :
      ell k ≤ dmin * mesh ∧ ell k ≤ dmin * R := by
    constructor
    · exact
        (he k).2.le.trans
          (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact
        (he k).2.le.trans
          (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)

  refine
    ⟨N, hN, ell, rmin, hr, hi, hS,
      fun k => ⟨(he k).1, hlo k, (hup k).1, (hup k).2⟩,
      ?_⟩

  intro d hd' hd'' k
  have hd0 : 0 < d := hdmin.trans_le hd'
  refine
    ⟨(le_div_iff₀ hd0).mpr ?_,
      (div_le_iff₀ hd0).mpr ?_,
      (div_le_iff₀ hd0).mpr ?_⟩

  · exact
      (by
        nlinarith [hr] : rmin * d ≤ dmax * rmin).trans (hlo k)
  · exact
      (hup k).1.trans (by nlinarith [hm])
  · exact
      (hup k).2.trans (by nlinarith [hR])

/-!
## Perturbed HighData structure
-/

/--
Additive scalar package at the fixed perturbed geometry.  It retains every
scalar field of the official `HighData`, changes only the slot-sum target to
`perturbedTotalE`, and adds the physical conductor cap, the slot-aware central
budget, and the slot-aware floor budget.
-/
structure HighDataPerturbedBudget (Δ B : ℝ) where
  t : ℝ
  N : ℕ
  ell : Fin N → ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  t_pos : 0 < t
  t_delta : t < Δ / 4
  t_small : t ≤ 1 / 100000000
  slots_pos : 0 < N
  slots_injective : Function.Injective ell
  slots_sum : (∑ j, ell j) = perturbedTotalE
  slots_bounds :
    ∀ j, 0 < ell j ∧ (7 / 8) * rmin ≤ ell j ∧ ell j ≤ (1 / 200) * t
  rmin_pos : 0 < rmin
  epsilon_pos : 0 < ε
  epsilon_small : ε ≤ 1 / 1000
  epsilon_gap : ε < rmin * t
  e_pos : 0 < e
  e_small : e < 1 / 1000
  kappa_pos : 0 < κ
  kappa_small : κ ≤ 1
  cost_pos : 0 < cost
  eps_pos : 0 < eps
  eps_small : eps ≤ 1
  sigma_pos : 0 < sigma
  detector_budget : 288 * e + 8 * κ + 2 * cost ≤ ε / 2
  phase_budget : 8 * e * t + κ ≤ ε
  count_budget : 159 * ε + t + t + 7 * t ≤ 1 / 32
  physical_conductor_cap : perturbedHeight + t + 2 * t ≤ 7 / 8
  central_budget :
    (13 / 16) * (159 * ε + t + t + 7 * t) + 2 * t +
      (3 / 2) * (2 * t) +
      (26 * e + (N + 8) * eps + t + t / 6) +
      (t + t + t) + t ≤ 49 / 440640
  new_central_budget :
    perturbedHeight * (159 * ε + t + t + 7 * t) + 2 * t +
      (3 / 2) * (2 * t) +
      (26 * e + (N + 8) * eps + t + perturbedTotalE * t) +
      (t + t + t) + t < B / 2
  geometric_budget : sigma + 8 * e + t / 8 ≤ 63 / 800
  principal_budget : sigma + t / 8 ≤ 17 / 48000
  saving_slot_quarter : sigma ≤ ((7 / 8) * rmin) / 4
  e_slot_quarter : e ≤ ((7 / 8) * rmin) / 4
  window_budget : sigma + e ≤ (7 / 8) * ((7 / 8) * rmin)
  window_boundary_budget : sigma + e ≤ perturbedBoundary * ((7 / 8) * rmin)
  floor_budget :
    2 * t + 26 * e + (N + 8) * eps + t + t / 6 + t / 8 + sigma ≤
      7 / 1200
  slot_aware_floor_budget :
    2 * t + 26 * e + (N + 8) * eps + t + perturbedTotalE * t +
        t / 8 + sigma ≤
      7 / 1200
  high_saving : sigma + t / 8 + t / 8 ≤ t
  height_choice :
    ∀ J : ℝ, 0 ≤ J →
      ∃ τ : ℝ, 0 < τ ∧ τ < (1 / 200) / 2 ∧
        4 * τ < (1 / 200) * cost ∧ τ < t ∧
        2 * τ * (1 + J) ≤ t ∧ τ * (2 + 4 * eps) < t

/-- Concrete specialization of the generic budget parameter. -/
abbrev HighDataPerturbed (Δ : ℝ) :=
  HighDataPerturbedBudget Δ perturbedBv6

/-!
## Constructors
-/

/--
Generic constructor with an arbitrary prescribed positive mesh.  The central
budget first chooses `t`; only then are slots selected with
`min t (mesh t)`, so there is no fixed-point dependence among `t`, `N`, and the
mesh.
-/
theorem exists_high_data_perturbed_budget_fine
    (Δ B : ℝ) (hΔ : 0 < Δ) (hB : 0 < B)
    (mesh : ℝ → ℝ) (hmesh : ∀ t : ℝ, 0 < t → 0 < mesh t) :
    ∃ D : HighDataPerturbedBudget Δ B,
      ∀ j, D.ell j ≤ mesh D.t / 200 := by
  let B_eff : ℝ := min B (49 / 440640)
  have hBcap : 0 < (49 / 440640 : ℝ) := by norm_num
  have hBeff : 0 < B_eff := by
    dsimp [B_eff]
    exact lt_min hB hBcap
  have hBeffB : B_eff ≤ B := by
    dsimp [B_eff]
    exact min_le_left _ _
  have hBeffOld : B_eff ≤ (49 / 440640 : ℝ) := by
    dsimp [B_eff]
    exact min_le_right _ _

  obtain ⟨t, ht, htΔ, ht1, hallow⟩ :=
    OAI.SevenEighths.CentralPerturbation.exists_perturbed_central_budget_with_slots
      Δ B_eff perturbedHeight perturbedTotalE
      hΔ hBeff perturbedHeight_nonneg perturbedHeight_le_one
      perturbedTotalE_nonneg perturbedTotalE_le_one

  obtain ⟨N, hN, ell, rmin, hr, hell, hsum, hbounds, hwidths⟩ :=
    exists_physical_slot_lengths_total_perturbed
      perturbedTotalE (1 / 200) (7 / 8) (min t (mesh t)) t
      perturbedTotalE_pos (by norm_num) (by norm_num)
      (lt_min ht (hmesh t ht)) ht

  obtain ⟨allowance, ha, hbudget⟩ := hallow N
  let small : ℝ := min allowance (t / ((N : ℝ) + 2000))
  have hsmall : 0 < small :=
    lt_min ha (div_pos ht (by positivity))
  have hsa : small ≤ allowance := min_le_left _ _
  have hst : small ≤ t / ((N : ℝ) + 2000) := min_le_right _ _
  have hst0 : small ≤ t / 2000 :=
    hst.trans
      (div_le_div_of_nonneg_left ht.le (by norm_num)
        (by linarith [Nat.cast_nonneg (α := ℝ) N]))

  let ellMin : ℝ := (7 / 8 : ℝ) * rmin
  have hmin : 0 < ellMin := mul_pos (by norm_num) hr

  obtain
      ⟨ε, e, κ, cost, _τdet,
        hε, hε1, hεgap, hεa,
        he, he1, heell, hea,
        hκ, hκ1, hcost, hdet, hphase,
        _hτdet, _hτd, _hτc, _hτloss, _hτeps⟩ :=
    exists_detector_scales
      t rmin t (1 / 200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)

  let eps : ℝ := small / 2
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have hepss : eps ≤ small := by
    dsimp [eps]
    linarith only [hsmall]
  have heps1 : eps ≤ 1 := by
    linarith only [hepss, hst0, ht1]

  have hbudget' :=
    hbudget ε e eps
      hε.le (hεa.trans hsa)
      he.le (hea.trans hsa)
      heps.le (hepss.trans hsa)

  have heN : ((N : ℝ) + 2000) * eps ≤ t := by
    have h :=
      (le_div_iff₀ (show 0 < (N : ℝ) + 2000 by positivity)).mp
        (hepss.trans hst)
    simpa only [mul_comm] using h

  have he8 : ((N : ℝ) + 8) * eps ≤ t := by
    nlinarith only [heN, heps.le]

  have het : 2000 * e ≤ t := by
    linarith only [hea, hst0]

  let sigma : ℝ := min (t / 2) (ellMin / 4)
  have hs : 0 < sigma :=
    lt_min (by positivity) (by positivity)
  have hst2 : sigma ≤ t / 2 := min_le_left _ _
  have hsell : sigma ≤ ellMin / 4 := min_le_right _ _

  have hEt : perturbedTotalE * t ≤ t :=
    mul_le_of_le_one_left ht.le perturbedTotalE_le_one

  have hphysical : perturbedHeight + t + 2 * t ≤ 7 / 8 :=
    perturbed_physical_conductor_cap_of_t_small ht1

  have hcount0 : 0 ≤ 159 * ε + t + t + 7 * t := by
    positivity

  have hheight_transfer :
      (13 / 16 : ℝ) * (159 * ε + t + t + 7 * t) ≤
        perturbedHeight * (159 * ε + t + t + 7 * t) :=
    mul_le_mul_of_nonneg_right
      thirteen_sixteenths_le_perturbedHeight hcount0

  have hslot_transfer : t / 6 ≤ perturbedTotalE * t := by
    calc
      t / 6 = (1 / 6 : ℝ) * t := by ring
      _ ≤ perturbedTotalE * t :=
        mul_le_mul_of_nonneg_right one_sixth_le_perturbedTotalE ht.le

  have hold_le_hnew :
      (13 / 16) * (159 * ε + t + t + 7 * t) + 2 * t +
          (3 / 2) * (2 * t) +
          (26 * e + (N + 8) * eps + t + t / 6) +
          (t + t + t) + t ≤
        perturbedHeight * (159 * ε + t + t + 7 * t) + 2 * t +
          (3 / 2) * (2 * t) +
          (26 * e + (N + 8) * eps + t + perturbedTotalE * t) +
          (t + t + t) + t := by
    linarith only [hheight_transfer, hslot_transfer]

  have hcentralOld :
      (13 / 16) * (159 * ε + t + t + 7 * t) + 2 * t +
          (3 / 2) * (2 * t) +
          (26 * e + (N + 8) * eps + t + t / 6) +
          (t + t + t) + t ≤
        49 / 440640 := by
    have hnew_le_eff := le_of_lt hbudget'.2
    have heff_half_old : B_eff / 2 ≤ (49 / 440640 : ℝ) := by
      linarith only [hBeffOld]
    exact hold_le_hnew.trans (hnew_le_eff.trans heff_half_old)

  have hcentralNew :
      perturbedHeight * (159 * ε + t + t + 7 * t) + 2 * t +
          (3 / 2) * (2 * t) +
          (26 * e + (N + 8) * eps + t + perturbedTotalE * t) +
          (t + t + t) + t <
        B / 2 := by
    exact hbudget'.2.trans_le (by linarith only [hBeffB])

  have hgeometric : sigma + 8 * e + t / 8 ≤ 63 / 800 := by
    linarith only [hst2, het, ht1, ht.le]

  have hprincipal : sigma + t / 8 ≤ 17 / 48000 := by
    linarith only [hst2, ht1, ht.le]

  have hwindow : sigma + e ≤ (7 / 8) * ellMin := by
    linarith only [hsell, heell, hmin]

  have hwindowNew : sigma + e ≤ perturbedBoundary * ellMin := by
    have hp := mul_le_mul_of_nonneg_right half_le_perturbedBoundary hmin.le
    linarith only [hsell, heell, hp]

  have hfloor :
      2 * t + 26 * e + (N + 8) * eps + t + t / 6 + t / 8 + sigma ≤
        7 / 1200 := by
    linarith only [hst2, het, he8, ht1, ht.le]

  have hslotFloor :
      2 * t + 26 * e + (N + 8) * eps + t + perturbedTotalE * t +
          t / 8 + sigma ≤
        7 / 1200 := by
    linarith only [hst2, het, he8, hEt, ht1, ht.le]

  have hhigh : sigma + t / 8 + t / 8 ≤ t := by
    linarith only [hst2, ht]

  let D : HighDataPerturbedBudget Δ B := {
    t := t
    N := N
    ell := ell
    rmin := rmin
    ε := ε
    e := e
    κ := κ
    cost := cost
    eps := eps
    sigma := sigma
    t_pos := ht
    t_delta := htΔ
    t_small := ht1
    slots_pos := hN
    slots_injective := hell
    slots_sum := hsum
    slots_bounds := fun j =>
      ⟨(hbounds j).1, (hbounds j).2.1, (hbounds j).2.2.2⟩
    rmin_pos := hr
    epsilon_pos := hε
    epsilon_small := hε1
    epsilon_gap := hεgap
    e_pos := he
    e_small := he1
    kappa_pos := hκ
    kappa_small := hκ1
    cost_pos := hcost
    eps_pos := heps
    eps_small := heps1
    sigma_pos := hs
    detector_budget := by
      linarith only [hdet]
    phase_budget := hphase
    count_budget := hbudget'.1
    physical_conductor_cap := hphysical
    central_budget := hcentralOld
    new_central_budget := hcentralNew
    geometric_budget := hgeometric
    principal_budget := hprincipal
    saving_slot_quarter := hsell
    e_slot_quarter := heell
    window_budget := by
      change sigma + e ≤ (7 / 8) * ellMin
      exact hwindow
    window_boundary_budget := hwindowNew
    floor_budget := hfloor
    slot_aware_floor_budget := hslotFloor
    high_saving := hhigh
    height_choice := by
      intro J hJ
      let τ : ℝ :=
        min ((1 / 200 : ℝ) * cost / 16)
          (min (1 / 800) (t / (4 * (J + 7))))
      have htau : 0 < τ :=
        lt_min (by positivity)
          (lt_min (by norm_num) (by positivity))
      have hτc : τ ≤ (1 / 200 : ℝ) * cost / 16 :=
        min_le_left _ _
      have hτd : τ ≤ 1 / 800 :=
        (min_le_right _ _).trans (min_le_left _ _)
      have hτt : τ ≤ t / (4 * (J + 7)) :=
        (min_le_right _ _).trans (min_le_right _ _)
      have hτJ : τ * (4 * (J + 7)) ≤ t :=
        (le_div_iff₀ (by positivity)).mp hτt
      have hprod : 0 ≤ τ * J := mul_nonneg htau.le hJ
      have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
      refine
        ⟨τ, htau,
          by linarith only [hτd],
          by linarith only [hτc, hcost],
          by nlinarith only [hτJ, hprod, htau],
          by nlinarith only [hτJ, hprod, htau],
          by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
  }

  refine ⟨D, ?_⟩
  intro j
  dsimp [D]
  calc
    ell j ≤ (1 / 200 : ℝ) * min t (mesh t) := (hbounds j).2.2.1
    _ ≤ (1 / 200 : ℝ) * mesh t :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
    _ = mesh t / 200 := by ring

/-- Generic constructor without a prescribed external mesh. -/
theorem exists_high_data_perturbed_budget
    (Δ B : ℝ) (hΔ : 0 < Δ) (hB : 0 < B) :
    Nonempty (HighDataPerturbedBudget Δ B) := by
  obtain ⟨D, _hD⟩ :=
    exists_high_data_perturbed_budget_fine
      Δ B hΔ hB (fun x => x) (by
        intro x hx
        exact hx)
  exact ⟨D⟩

/-- Concrete `Bv6` constructor. -/
theorem exists_high_data_perturbed
    (Δ : ℝ) (hΔ : 0 < Δ) :
    Nonempty (HighDataPerturbed Δ) := by
  simpa [HighDataPerturbed] using
    (exists_high_data_perturbed_budget
      Δ perturbedBv6 hΔ perturbedBv6_pos)

/-- Concrete `Bv6` constructor with an arbitrary prescribed positive mesh. -/
theorem exists_high_data_perturbed_fine
    (Δ : ℝ) (hΔ : 0 < Δ)
    (mesh : ℝ → ℝ) (hmesh : ∀ t : ℝ, 0 < t → 0 < mesh t) :
    ∃ D : HighDataPerturbed Δ,
      ∀ j, D.ell j ≤ mesh D.t / 200 := by
  simpa [HighDataPerturbed] using
    (exists_high_data_perturbed_budget_fine
      Δ perturbedBv6 hΔ perturbedBv6_pos mesh hmesh)

end SevenEighths.Parameters

end
end OAI

#check OAI.SevenEighths.Parameters.HighDataPerturbedBudget
#check OAI.SevenEighths.Parameters.HighDataPerturbed
#check OAI.SevenEighths.Parameters.exists_distinct_slot_lengths_total_perturbed
#check OAI.SevenEighths.Parameters.exists_physical_slot_lengths_total_perturbed
#check OAI.SevenEighths.Parameters.exists_high_data_perturbed_budget
#check OAI.SevenEighths.Parameters.exists_high_data_perturbed
#check OAI.SevenEighths.Parameters.exists_high_data_perturbed_fine

#print axioms OAI.SevenEighths.Parameters.exists_distinct_slot_lengths_total_perturbed
#print axioms OAI.SevenEighths.Parameters.exists_physical_slot_lengths_total_perturbed
#print axioms OAI.SevenEighths.Parameters.exists_high_data_perturbed_budget
#print axioms OAI.SevenEighths.Parameters.exists_high_data_perturbed
#print axioms OAI.SevenEighths.Parameters.exists_high_data_perturbed_fine
