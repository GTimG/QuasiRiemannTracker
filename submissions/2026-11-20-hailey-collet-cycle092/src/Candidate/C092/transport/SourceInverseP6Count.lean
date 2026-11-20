/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual same-zero inverse count with true original descriptor repetition. -/
import Candidate.C092.transport.SourceInverseP6Union

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ContDiff
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentWholeSlotDeletion HeckeDetectorRowwisePolynomial
open HeckeDetectorInverseFiberCount HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open Qrh.MarkedAnchor.Interface QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_SourceInverseP6Count_288e8bca4a38995c_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem same_zero_inverse_count {Label : Type*}
    (rows : Finset FreeRow) (χ : FreeRow→Label→Character)
    (U a ε cutoff T allowance : ℝ) (i : ℕ)
    (ws : ∀ u : rows,SupportedWitness (χ u.val) U a ε cutoff T allowance i)
    (label : Label) (r : ℝ) (hlabel : ∀ u,(ws u).label=label) (hr : ∀ u,(ws u).r=r)
    (mark : FreeRow→ℂ) (K : ℕ) (w e buffer εm C height : ℝ)
    (hU : 1<U) (ha : 1/2≤a) (hC : 0≤C) (hh : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hlower : ∀ u∈rows,U^(e*w-buffer)≤‖mark u‖^2)
    (hmoment : ∀ n : ℕ,n≤2 → ∀ σ∈Icc (0:ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) true ((logProfile^[n]) (inverseTest U cutoff r))
        (U^r) σ t*(mark u)^K‖^2 ≤ C*U^(1+εm)) :
    (rows.card : ℝ) ≤ (12*(1+height)*C)*U^(1-(2*a-1)*r-e*((K:ℝ)*w)+2*ε+(K:ℝ)*buffer+εm) := by
  let χ' := fun u : rows => χ u.val
  let wit := fun u : rows => (ws u).toWitness
  have hUp := zero_lt_one.trans hU
  have hs (u : rows) : U^((2*a-1)*r-2*ε) ≤
      ‖polynomial (χ' u label) true (inverseTest U cutoff r) (U^r)
        (wit u).zero.re (wit u).frequency‖^2 := by
    simpa only [χ',wit,inverseTest,hr u,hlabel u,Witness.frequency] using (ws u).inverse_spike
  have hm := HeckeDetectorFiberEnergy.inverse_energy Finset.univ χ' U a ε cutoff T allowance i
    (by linarith) wit label (inverseTest U cutoff r) (U^r) (1/4) (9/4) (C*U^(1+εm))
    (fun u => (mark u.val)^K) (Real.rpow_pos_of_pos hUp _) (by norm_num)
    (HeckeDetectorDyadicActual.inverse_profile_support _ _) (by positivity) height hh hfreq
    (by
      intro n hn σ hσ t ht
      dsimp only [χ']
      rw [Finset.sum_coe_sort rows (fun u : FreeRow =>
        ‖polynomial (χ u label) true ((logProfile^[n]) (inverseTest U cutoff r)) (U^r) σ t*(mark u)^K‖^2)]
      exact hmoment n hn σ hσ t ht)
  have he : (∑ u : rows,‖polynomial (χ' u label) true (inverseTest U cutoff r) (U^r)
      (wit u).zero.re (wit u).frequency*(mark u.val)^K‖^2) ≤
      (12*(1+height)*C)*U^(1+εm) := by convert hm using 1 <;> ring
  have hp (u : rows) : U^(2*(e/2)*((K:ℝ)*w)-(K:ℝ)*buffer) ≤ ‖(mark u.val)^K‖^2 := by
    have h := pow_le_pow_left₀ (Real.rpow_pos_of_pos hUp _).le (hlower u.val u.property) K
    rw [←Real.rpow_mul_natCast hUp.le] at h
    convert h using 1
    · congr 1
      ring
    · simp only [norm_pow,←pow_mul,Nat.mul_comm]
  have hc := HeckeDetectorRowCount.inverse_count Finset.univ (fun u : rows => χ' u label)
    (inverseTest U cutoff r) (U^r) (fun u => (wit u).zero.re) (fun u => (wit u).frequency)
    (fun u => (mark u.val)^K) U (2*a-1) r (e/2) ((K:ℝ)*w) (2*ε) ((K:ℝ)*buffer) εm
    (12*(1+height)*C) hUp (fun u _ => hs u) (fun u _ => hp u) he
  simpa only [Finset.card_univ,Fintype.card_coe, mul_div_cancel₀ e (by norm_num : (2:ℝ)≠0)] using hc

#print axioms same_zero_inverse_count
end
end QRH.Cycle092.SourceInverseP6
