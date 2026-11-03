/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalHigh/Parameters.lean
Original SHA-256: de9af9a9d151cf9e38b6f0c4b54d12adf94521c154f12ace53d7df138ddd288d
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.DistinctSlots
import Submissions.lw56e2_parameter_refinement.Transport.TunedCandidate
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersDetectorScales

/-!
# Parameter choice independent of the old boundary gap

The energy mesh and a positive high-side loss are chosen first. One then
chooses an arbitrarily large even number of distinct slots. Detector and
low-side errors may be made arbitrarily small after those slots are fixed.
The height exponent is chosen last, after the actual moment degree exists.
-/

namespace LW56e2.Transport.PhysicalHigh
noncomputable section
open scoped BigOperators

/-- A size choice usable with any fixed canonical realization of the
`distinct_slots_for_size` bounds. -/
theorem fine_even_slot_count (cap : ℝ) (hcap : 0 < cap) (Kmin : ℕ) :
    ∃ K : ℕ, Kmin ≤ K ∧ 0 < K ∧ Even K ∧
      2 * TunedCandidate.ell / K ≤ cap := by
  have ht : 0 < TunedCandidate.ell := by
    norm_num [TunedCandidate.ell, Geometry.ell, TunedCandidate.p]
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 * TunedCandidate.ell / cap) (Kmin : ℝ))
  have hnc : 2 * TunedCandidate.ell / cap < (n : ℝ) :=
    (le_max_left _ _).trans_lt hn
  have hnk : (Kmin : ℝ) < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := (div_pos (by positivity) hcap).trans hnc
    exact_mod_cast this
  have hK : 0 < 2 * n := by omega
  have hKp : (0 : ℝ) < (2 * n : ℕ) := by exact_mod_cast hK
  have hcapK : 2 * TunedCandidate.ell / (2 * n : ℕ) ≤ cap := by
    apply (div_le_iff₀ hKp).mpr
    have hh := (div_lt_iff₀ hcap).mp hnc
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  refine ⟨2 * n, ?_, hK, ⟨n, by omega⟩, hcapK⟩
  have : Kmin < n := by exact_mod_cast hnk
  omega

/-- Arbitrarily fine distinct slots with the tuned total; `Kmin` can encode
all previously fixed lower bounds on the number of slots. -/
theorem fine_even_slots (cap : ℝ) (hcap : 0 < cap) (Kmin : ℕ) :
    ∃ K : ℕ, Kmin ≤ K ∧ 0 < K ∧ Even K ∧
      ∃ ell : Fin K → ℝ, Function.Injective ell ∧
      (∑ j, ell j) = TunedCandidate.ell ∧
      ∀ j, TunedCandidate.ell / (2 * K) ≤ ell j ∧ ell j ≤ cap := by
  have ht : 0 < TunedCandidate.ell := by
    norm_num [TunedCandidate.ell, Geometry.ell, TunedCandidate.p]
  obtain ⟨K, hKmin, hK, hEven, hcapK⟩ := fine_even_slot_count cap hcap Kmin
  obtain ⟨ell, hinj, hsum, hbounds⟩ :=
    distinct_slots_for_size TunedCandidate.ell ht K hK
  exact ⟨K, hKmin, hK, hEven, ell, hinj, hsum,
    fun j => ⟨(hbounds j).1, (hbounds j).2.le.trans hcapK⟩⟩

/-- The post-slot errors. No old-boundary gap occurs in these fields. -/
structure DetectorScales (t : ℝ) (K : ℕ) (rmin ellMin allowance : ℝ) where
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  epsilon_pos : 0 < ε
  epsilon_small : ε ≤ 1 / 1000
  epsilon_gap : ε < rmin * t
  epsilon_allowance : ε ≤ allowance
  e_pos : 0 < e
  e_small : e < 1 / 1000
  e_slot : e ≤ ellMin / 4
  e_allowance : e ≤ allowance
  kappa_pos : 0 < κ
  kappa_small : κ ≤ 1
  cost_pos : 0 < cost
  eps_pos : 0 < eps
  eps_small : eps ≤ 1
  eps_allowance : eps ≤ allowance
  sigma_pos : 0 < sigma
  sigma_t : sigma ≤ t / 2
  sigma_slot : sigma ≤ ellMin / 4
  sigma_allowance : sigma ≤ allowance
  detector_budget : 288 * e + 8 * κ + 2 * cost ≤ ε / 2
  phase_budget : 8 * e * t + κ ≤ ε
  central_budget : (159 * ε + t + t + 7 * t) + 2 * t +
    (26 * e + (K + 8) * eps + t + t * TunedCandidate.ell) +
    (t + t + t) + t ≤ 18 * t
  height_choice : ∀ J : ℝ, 0 ≤ J → ∃ τ : ℝ,
    0 < τ ∧ τ < (1 / 200 : ℝ) / 2 ∧
    4 * τ < (1 / 200 : ℝ) * cost ∧ τ < t ∧
    2 * τ * (1 + J) ≤ t ∧ τ * (2 + 4 * eps) < t

/-- After the slots have been fixed, every requested positive error ceiling
can be met while preserving the high-side budget. -/
theorem exists_detector_scales_after_slots
    (t rmin ellMin allowance : ℝ) (K : ℕ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hr : 0 < rmin)
    (hell : 0 < ellMin) (ha : 0 < allowance) :
    Nonempty (DetectorScales t K rmin ellMin allowance) := by
  let small := min allowance (t / ((K : ℝ) + 2000))
  have hsmall : 0 < small := lt_min ha (div_pos ht (by positivity))
  have hsa : small ≤ allowance := min_le_left _ _
  have hst : small ≤ t / ((K : ℝ) + 2000) := min_le_right _ _
  have hst0 : small ≤ t / 2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num)
      (by linarith [Nat.cast_nonneg (α := ℝ) K]))
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
      hdet,hphase,_,_,_,_,_⟩ :=
    OAI.SevenEighths.Parameters.exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hell hsmall (by norm_num)
  let eps := small / 2
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hepss : eps ≤ small := by dsimp [eps]; linarith only [hsmall]
  have heps1 : eps ≤ 1 := by linarith only [hepss, hst0, ht1]
  have heN : ((K : ℝ) + 2000) * eps ≤ t := by
    have h := (le_div_iff₀ (show 0 < (K : ℝ) + 2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((K : ℝ) + 8) * eps ≤ t := by nlinarith only [heN, heps.le]
  have het : 2000 * e ≤ t := by linarith only [hea, hst0]
  have hεt : 2000 * ε ≤ t := by linarith only [hεa, hst0]
  have htotal : TunedCandidate.ell ≤ 1/2 := by
    norm_num [TunedCandidate.ell, Geometry.ell, TunedCandidate.p]
  let sigma := min (t / 2) (min (ellMin / 4) allowance)
  have hs : 0 < sigma := lt_min (by positivity) (lt_min (by positivity) ha)
  have hst2 : sigma ≤ t / 2 := min_le_left _ _
  have hsell : sigma ≤ ellMin / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hsa' : sigma ≤ allowance := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨{
    ε := ε, e := e, κ := κ, cost := cost, eps := eps, sigma := sigma
    epsilon_pos := hε, epsilon_small := hε1, epsilon_gap := hεgap
    epsilon_allowance := hεa.trans hsa
    e_pos := he, e_small := he1, e_slot := heell, e_allowance := hea.trans hsa
    kappa_pos := hκ, kappa_small := hκ1, cost_pos := hcost
    eps_pos := heps, eps_small := heps1, eps_allowance := hepss.trans hsa
    sigma_pos := hs, sigma_t := hst2, sigma_slot := hsell, sigma_allowance := hsa'
    detector_budget := by linarith only [hdet]
    phase_budget := hphase
    central_budget := ?_
    height_choice := ?_ }⟩
  · have htell : t * TunedCandidate.ell ≤ t/2 := by nlinarith
    linarith only [hεt, het, he8, htell, ht]
  · intro J hJ
    let τ := min ((1/200 : ℝ) * cost / 16) (min (1/800) (t / (4 * (J + 7))))
    have htau : 0 < τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτc : τ ≤ (1/200 : ℝ) * cost / 16 := min_le_left _ _
    have hτd : τ ≤ 1/800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτt : τ ≤ t / (4 * (J + 7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ * (4 * (J + 7)) ≤ t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0 ≤ τ * J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨τ, htau, by linarith only [hτd], by linarith only [hτc, hcost],
      by nlinarith only [hτJ, hprod, htau], by nlinarith only [hτJ, hprod, htau],
      by nlinarith only [hτJ, hprod, hprodeps, htau]⟩

end
end LW56e2.Transport.PhysicalHigh
