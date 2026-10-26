import Candidate.Target830.Physical.Geometry
import Candidate.Cycle25.Numerator.SourceSelection
import Candidate.Cycle25.Numerator.AmplitudeHolder
import Candidate.Cycle25.Numerator.BoxReconstruction
import Candidate.Cycle25.Numerator.ActualBin
import Candidate.Target830.Physical.Active
import Candidate.Target830.Physical.Data
import Candidate.Cycle25.Numerator.PhysicalFront

/- Original module: Candidate.Target830.Physical.Selection. -/
section

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

namespace OAI.SevenEighths.Target830.Physical
open Cycle25.Numerator
open HeckeDetectorPhysicalSelection

/-- Selection on the original full slot family, with error gains zeroed.
The cardinality, labels and row polynomials are not changed. -/
theorem scheduled_whole_slots (P : SourcePlane) {Slot : Type*}
    [Fintype Slot] [DecidableEq Slot]
    (d v delta mesh : ℝ) (hd : dMinus ≤ d ∧ d ≤ dPlus)
    (hv : 0 ≤ v) (hdelta : 0 ≤ delta) (hmesh : 0 < mesh)
    (widths : Slot → ℝ) (hw : ∀ j, 0 ≤ widths j)
    (hwm : ∀ j, widths j ≤ mesh) (hsum : ∑ j, widths j = ell / d)
    (main : Finset Slot) (g : Slot → ℝ)
    (hg : ∀ j, 0 ≤ g j ∧ g j ≤ delta / 2)
    (herror : ∀ j, j ∉ main → g j = 0) :
    let a := weightedMean Finset.univ widths g
    a = (∑ j, widths j * g j) / (ell / d) ∧ 0 ≤ a ∧ a ≤ delta / 2 ∧
    ∃ selected : Finset Slot, selected ⊆ main ∧ (∀ j ∈ selected, 0 < g j) ∧
      (∑ j ∈ selected, widths j) ≤ scheduledCapacity P d v ∧
      a * scheduledCapacity P d v - (delta / 2) * mesh ≤
        ∑ j ∈ selected, widths j * g j ∧
      ∀ U : ℝ, 1 ≤ U → ∀ Q : Slot → ℂ,
        (∀ j, 0 < g j → U ^ (2 * widths j * g j) ≤ ‖Q j‖ ^ 2) →
        U ^ (2 * a * scheduledCapacity P d v - delta * mesh) ≤
          ‖∏ j ∈ selected, Q j‖ ^ 2 := by
  have hdpos := physical_d_pos hd.1
  have hell : 0 < ell := by norm_num [ell, theta]
  have hL : 0 < ∑ j, widths j := by rw [hsum]; exact div_pos hell hdpos
  have hcap : scheduledCapacity P d v ≤ ∑ j, widths j := by
    rw [hsum]
    exact scheduledCapacity_le_supply P hd hv
  obtain ⟨ha, had⟩ := weightedMean_bounds Finset.univ widths g delta
    (fun j _ => hw j) hL (fun j _ => hg j)
  obtain ⟨T, _, hT, hTpos, hTcap, hgain, hspike⟩ := SlotSelection.zero_error_whole_slots
    Finset.univ main widths g delta mesh (scheduledCapacity P d v)
    hdelta hmesh.le (fun j _ => hw j) (fun j _ => hwm j) hL
    (fun j _ => hg j) (fun j _ => herror j)
    (scheduledCapacity_nonneg P hd hv) hcap
  refine ⟨?_, ha, had, T, hT, hTpos, hTcap, hgain, ?_⟩
  · unfold weightedMean
    rw [hsum]
  · intro U hU Q hQ
    exact hspike U hU Q (fun j _ => hQ j)

end OAI.SevenEighths.Target830.Physical

#print axioms OAI.SevenEighths.Target830.Physical.scheduled_whole_slots
end

/- Original module: Candidate.Target830.Physical.BinBound. -/
section
/- Target830 actual physical specialization, adapted from accepted .874836.
Predecessor attribution retained. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

/- Adapted from Cycle25/Numerator/AmplitudeHolder.lean and its
akashlevy/QuasiRiemannTracker Apache-2.0 predecessor. The selected capacity
is the explicit Cycle63 schedule; the fourth moment is an input. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace OAI.SevenEighths.Target830.Physical.Packet
open OAI.SevenEighths.Target830 OAI.SevenEighths.Target830.Physical
open Cycle25.Numerator

theorem weighted_dilation_bin (plane : SourcePlane) {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (d U R q L v xi ann delta loss epsilon Ccount Cmoment : ℝ)
    (hd : dMinus ≤ d ∧ d ≤ dPlus)
    (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta / 2) (hv : 0 ≤ v) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hcard : (s.card : ℝ) ≤ Ccount * U^R)
    (hselected : ∀ i ∈ s, U^(q*scheduledCapacity plane d (2*(v+xi+ann))-loss) ≤ ‖Q i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^(q*L))
    (henergy : (∑ i ∈ s, ‖S i‖^4 * ‖Q i‖^2) ≤ Cmoment * U^(1+epsilon)) :
    U^(-delta*v/2) * (∑ i ∈ s, ‖S i * P i‖) ≤
      Ccount * Cmoment * U^(q*L-q*zeroCapacity plane d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2-
        2*dampingRate*delta*(v+xi+ann)) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hh := weighted_amplitude_bin s S Q P U R (q*L)
    (q*scheduledCapacity plane d (2*(v+xi+ann))-loss) epsilon Ccount Cmoment hU0 hc hm
    hcard hselected hfull henergy
  have hdelta : 0 ≤ delta := by linarith
  have hdamp := scheduled_capacity_damping plane hd (by positivity : 0 ≤ 2*(v+xi+ann)) hq hqdelta hdelta
  calc
    _ ≤ U^(-delta*v/2) *
        (Ccount*Cmoment*U^(q*L-(q*scheduledCapacity plane d (2*(v+xi+ann))-loss)/2+(3*R+1+epsilon)/4)) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hU0.le _)
    _ = (Ccount*Cmoment) * (U^(-delta*v/2) *
        U^(q*L-(q*scheduledCapacity plane d (2*(v+xi+ann))-loss)/2+(3*R+1+epsilon)/4)) := by ring
    _ = Ccount*Cmoment*U^(-delta*v/2+q*L-
        (q*scheduledCapacity plane d (2*(v+xi+ann))-loss)/2+(3*R+1+epsilon)/4) := by
      rw [←Real.rpow_add hU0]
      congr 1
      congr 1
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by have hc0 := le_trans zero_le_one hc; have hm0 := le_trans zero_le_one hm; positivity)
      apply Real.rpow_le_rpow_of_exponent_le hU
      linarith


end OAI.SevenEighths.Target830.Physical.Packet

#print axioms OAI.SevenEighths.Target830.Physical.Packet.weighted_dilation_bin
end

/- Original module: Candidate.Target830.Physical.FiniteBins. -/
section
/- Target830 actual physical specialization, adapted from accepted .874836.
Predecessor attribution retained. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

/-! Finite dilation boxes summed after the weighted fourth-moment estimate.
The coefficient mass stays a single linear factor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace OAI.SevenEighths.Target830.Physical.Packet
open OAI.SevenEighths.Target830 OAI.SevenEighths.Target830.Physical
open Cycle25.Numerator

theorem finite_weighted_dilation_bins (plane : SourcePlane) {ι : Type*} (s : Finset ι) (n : ℕ)
    (S Q : ℕ → ι → ℂ) (P f : ι → ℂ)
    (d U R q L xi ann delta loss epsilon Ccount Cmoment M : ℝ)
    (hd : dMinus ≤ d ∧ d ≤ dPlus)
    (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment) (hM : 0 ≤ M)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta/2) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hcard : (s.card : ℝ) ≤ Ccount*U^R)
    (hsplit : ∀ i ∈ s, f i = ∑ j ∈ Finset.range (n+1),
      ((M * U^(-delta*((j : ℝ)*xi)/2) : ℝ) : ℂ) * S j i)
    (hselected : ∀ j ∈ Finset.range (n+1), ∀ i ∈ s,
      U^(q*scheduledCapacity plane d (2*((j : ℝ)*xi+xi+ann))-loss) ≤ ‖Q j i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^(q*L))
    (henergy : ∀ j ∈ Finset.range (n+1),
      (∑ i ∈ s, ‖S j i‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i ∈ s, ‖f i * P i‖) ≤
      ((n+1 : ℕ) : ℝ)*M*Ccount*Cmoment*
        U^(q*L-q*zeroCapacity plane d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hdelta : 0 ≤ delta := by linarith
  let E : ℝ := q*L-q*zeroCapacity plane d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2
  have hj (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∑ i ∈ s, ‖(((M * U^(-delta*((j : ℝ)*xi)/2) : ℝ) : ℂ) * S j i) * P i‖) ≤
      M*Ccount*Cmoment*U^E := by
    have hb := weighted_dilation_bin plane s (S j) (Q j) P d U R q L ((j : ℝ)*xi) xi ann delta
      loss epsilon Ccount Cmoment hd hU hc hm hq hqdelta (mul_nonneg (Nat.cast_nonneg _) hxi)
      hxi hann hcard (hselected j hj) hfull (henergy j hj)
    have hpow : U^(E-2*dampingRate*delta*((j : ℝ)*xi+xi+ann)) ≤ U^E :=
      Real.rpow_le_rpow_of_exponent_le hU (by
        have hv : 0 ≤ (j : ℝ)*xi+xi+ann := by positivity
        have := mul_nonneg (mul_nonneg (by norm_num [dampingRate] : (0:ℝ)≤ dampingRate) hdelta) hv
        dsimp only [E]
        nlinarith)
    calc
      _ = M * (U^(-delta*((j : ℝ)*xi)/2) * (∑ i ∈ s, ‖S j i * P i‖)) := by
        rw [Finset.mul_sum,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_assoc,norm_mul,Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg hM (Real.rpow_nonneg hU0.le _))]
        ring
      _ ≤ M * (Ccount*Cmoment*U^(E-2*dampingRate*delta*((j : ℝ)*xi+xi+ann))) :=
        mul_le_mul_of_nonneg_left hb hM
      _ ≤ M * (Ccount*Cmoment*U^E) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow (by have hc0 := zero_le_one.trans hc; have hm0 := zero_le_one.trans hm; positivity)) hM
      _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ Finset.range (n+1),
        ‖(((M * U^(-delta*((j : ℝ)*xi)/2) : ℝ) : ℂ) * S j i) * P i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [hsplit i hi,Finset.sum_mul]
      exact norm_sum_le _ _
    _ = ∑ j ∈ Finset.range (n+1), ∑ i ∈ s,
        ‖(((M * U^(-delta*((j : ℝ)*xi)/2) : ℝ) : ℂ) * S j i) * P i‖ := Finset.sum_comm
    _ ≤ ∑ j ∈ Finset.range (n+1), M*Ccount*Cmoment*U^E := Finset.sum_le_sum hj
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; dsimp only [E]; ring

end OAI.SevenEighths.Target830.Physical.Packet


/- Adapted from Cycle25/Numerator/FiniteBins.lean; original predecessor:
akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/

#print axioms OAI.SevenEighths.Target830.Physical.Packet.finite_weighted_dilation_bins
end

/- Original module: Candidate.Target830.Physical.PacketBound. -/
section
/- Target830 actual physical specialization, adapted from accepted .874836.
Predecessor attribution retained. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

/-! Infinite coefficient sums are reconstructed by the existing normalized-box
lemmas. The rowwise fourth moment remains an explicit integration input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace OAI.SevenEighths.Target830.Physical.Packet
open OAI.SevenEighths.Target830 OAI.SevenEighths.Target830.Physical
open Cycle25.Numerator

variable {ι : Type*} [Fintype ι] {α : ι → Type*}

theorem packet_weighted_bins (plane : SourcePlane)
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (Lc : ι → ℝ) (d U xi ann : ℝ) (n : ℕ)
    (valid : ∀ i, α i → Prop) [∀ i e, Decidable (valid i e)]
    (Q : ℕ → ι → ℂ) (P : ι → ℂ)
    (R q L delta loss epsilon Ccount Cmoment M : ℝ)
    (hd : dMinus ≤ d ∧ d ≤ dPlus) (hM : 0 < M) (hU : 1 ≤ U) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment) (hq : 0 ≤ q) (hqdelta : q ≤ delta/2)
    (hcard : (Fintype.card ι : ℝ) ≤ Ccount*U^R)
    (hzero : ∀ i e, ¬valid i e → S i e = 0)
    (hupper : ∀ i e, valid i e → max 1 (Lc i * N i e) ≤ U^((n : ℝ)*xi))
    (hseries : ∀ i, Summable (fun e=>‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e‖))
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (Lc i * N i e)^(delta/2)))
    (hmass : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (Lc i * N i e)^(delta/2)) ≤ M)
    (hselected : ∀ j ∈ Finset.range (n+1), ∀ i,
      U^(q*scheduledCapacity plane d (2*((j : ℝ)*xi+xi+ann))-loss) ≤ ‖Q j i‖)
    (hfull : ∀ i, ‖P i‖ ≤ U^(q*L))
    (hselection : ∀ j ∈ Finset.range (n+1), ∀ e : ∀ i, α i,
      (∑ i, ‖if valid i (e i) ∧ dilationBox U xi n (max 1 (Lc i*N i (e i))) = j
        then S i (e i) else 0‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i, ‖(∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)*P i‖) ≤
      ((n+1 : ℕ) : ℝ)*M*Ccount*Cmoment*
        U^(q*L-q*zeroCapacity plane d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hrho : 0 ≤ delta/2 := by linarith
  let B (j : ℕ) (i : ι) := normalizedBox U xi n j (delta/2) M
    (fun e=> max 1 (Lc i*N i e)) (fun e=> A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)
  have hsplit (i : ι) : (∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) =
      ∑ j ∈ Finset.range (n+1), ((M*U^(-delta*((j : ℝ)*xi)/2) : ℝ):ℂ)*B j i := by
    have hh := normalized_box_reconstruction U xi n (delta/2) M hU0 hM.ne'
      (fun e=> max 1 (Lc i*N i e)) (fun e=> A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) (hseries i)
    have hexp (j : ℕ) : -(delta/2)*((j : ℝ)*xi) = -delta*((j : ℝ)*xi)/2 := by ring
    simpa only [hexp, B] using hh
  have henergy (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∑ i, ‖B j i‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon) :=
    normalized_dilation_box_fourth base A S N hN Lc (delta/2) U xi n j valid (Q j) M
      (Cmoment*U^(1+epsilon)) hM hU hxi hrho hzero hupper hs hmass (hselection j hj)
  exact finite_weighted_dilation_bins plane Finset.univ n B Q P _ d U R q L xi ann delta loss epsilon
    Ccount Cmoment M hd hU hc hm hM.le hq hqdelta hxi hann (by simpa using hcard)
    (fun i hi=> hsplit i) (fun j hj i hi=> hselected j hj i) (fun i hi=> hfull i) henergy


end OAI.SevenEighths.Target830.Physical.Packet

#print axioms OAI.SevenEighths.Target830.Physical.Packet.packet_weighted_bins
end

/- Original module: Candidate.Target830.Physical.ActualBin. -/
section
/- Target830 actual physical specialization, adapted from accepted .874836.
Predecessor attribution retained. Apache-2.0. -/
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators Classical ContDiff
namespace OAI.SevenEighths.Target830.Physical.Packet
open OAI.SevenEighths.Target830 OAI.SevenEighths.Target830.Physical Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
local notation "O" => HeckeFamily.O

theorem actual_label_packet_bin_bound (plane : SourcePlane) {ι : Type} [Fintype ι] [DecidableEq ι]
    (massEps cp dp Bp : ℝ) (hmassEps : 0 < massEps)
    (hcp : 0 < cp) (hdp : 0 < dp) (hBp : 0 ≤ Bp) :
    ∃ Cmass : ℝ, 0 < Cmass ∧ ∀
      (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character)
      (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
      (hdis : ∀P:∀i,T i,Function.Injective (fun i=>(P i).val))
      (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
      (Pbase : ∀i,T i) (W : ι→ℝ→ℂ) (Yp : ι→ℝ),
      (∀i,1≤ Yp i) → (∀i,Function.support (W i)⊆Set.Icc cp dp) →
      (∀i y,‖W i y‖≤ Bp) → ∀(x z : ℂ) (alpha eps : ℝ),
      51/100≤ alpha → alpha≤1 → 0< eps → eps≤1/1000 →
      x.re=alpha+16*eps → z.re=17/50 →
      ∀(κ : Type) [Fintype κ] (u : κ→FreeRow)
      (W1 : ℝ→ℂ) (a b Y : ℝ), 0< a → Function.support W1⊆Set.Icc a b →
      ContDiff ℝ ∞ W1 → 0< Y →
      ∀(d U xi ann : ℝ) (n : ℕ) (Cu : κ→ℝ) (Ccond : ℝ)
      (Q : ℕ→κ→ℂ) (P : κ→ℂ)
      (R q L delta loss momentEps Ccount Cmoment : ℝ),
      dMinus≤ d ∧ d≤ dPlus → 1≤ U → 0≤ xi → 0≤ ann → 1≤ Ccount → 1≤ Cmoment → 0≤ q → q≤ delta/2 →
      0≤ delta/2 → delta/2≤1 →
      1-alpha-6*eps≤1/2-delta/2 → -(1/100:ℝ)≤1/2-delta/2 →
      1+firsteps≤ x.re+(1/2-delta/2) → 0< Ccond →
      (∀i,0≤ Cu i) → (∀i,Cu i≤ Ccond*((Ideal.span {(u i).val}:Ideal O).radical.absNorm:ℝ)) →
      (∀i,((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ)≤ U) →
      (∀i,(rowCharacter S hS.prime (u i)).residue≠1) →
      b*Y≤ U^((n:ℝ)*xi) →
      (Fintype.card κ:ℝ)≤ Ccount*U^R →
      (∀j∈Finset.range (n+1),∀i,U^(q*scheduledCapacity plane d (2*((j:ℝ)*xi+xi+ann))-loss)≤‖Q j i‖) →
      (∀i,‖P i‖≤ U^(q*L)) →
      let Lc (i : κ) := Cu i/(Ccond*((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ))
      (∀j∈Finset.range (n+1),∀e:∀i,LabelPacketIndex S (u i) T,
        (∑i,‖if (labelPacketScale S (u i) T (e i):ℝ)≤ b*Y ∧
          dilationBox U xi n (max 1 (Lc i*(labelPacketScale S (u i) T (e i):ℝ)))=j
          then HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1
            (Y/(labelPacketScale S (u i) T (e i):ℝ)) 0 0 else 0‖^4 * ‖Q j i‖^2)
          ≤ Cmoment*U^(1+momentEps)) →
      (∑i,‖labelPolynomialPacket S hS η (u i) T hT W Yp x z W1 Y*P i‖) ≤
        Y^(-(1/2:ℝ))*((n+1:ℕ):ℝ)*(Cmass*U^massEps*∏i,(Yp i)^(-(4/25:ℝ)))*
          Ccount*Cmoment*U^(q*L-q*zeroCapacity plane d/2+(3*R+1+momentEps)/4+loss/2+delta*(xi+ann)/2) := by
  obtain ⟨Cmass,hCmass,hmass⟩ := actual_physical_label_mass (ι:=ι) massEps cp dp Bp hmassEps hcp hdp hBp
  refine ⟨Cmass,hCmass,?_⟩
  intro S hS firsteps hfirst η T hT hdis hη Pbase W Yp hYp hWS hWB x z alpha eps
    halpha halpha1 heps heps1 hx hz κ _ u W1 a b Y ha hsupp hW1 hY d U xi ann n Cu Ccond Q P
    R q L delta loss momentEps Ccount Cmoment hd hU hxi hann hc hm hq hqdelta hrho hrho1
    hline hleft hmargin hCcond hCu0 hCu hNu hrow hcut hcard hselected hfull Lc hselection
  let weight : ∀i,T i→ℂ := fun i P=> physicalSlotWeight P.val (W i) (Yp i) z
  let A (i : κ) := labelPacketCoefficient S hS η (u i) T hT weight x z
  let N (i : κ) (e : LabelPacketIndex S (u i) T) : ℝ := labelPacketScale S (u i) T e
  let Sp (i : κ) (e : LabelPacketIndex S (u i) T) :=
    HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1 (Y/N i e) 0 0
  let M : ℝ := Cmass*U^massEps*∏i,(Yp i)^(-(4/25:ℝ))
  have hU0 : 0< U := lt_of_lt_of_le zero_lt_one hU
  have hNp (i : κ) (e : LabelPacketIndex S (u i) T) : 0< N i e :=
    lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S (u i) T e)
  have hM : 0< M := mul_pos (mul_pos hCmass (Real.rpow_pos_of_pos hU0 _))
    (Finset.prod_pos (fun i _=> Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (hYp i)) _))
  have hLM (i : κ) : Lc i ≤ 1 := by
    letI : Finite (O ⧸ (Ideal.span {(u i).val}:Ideal O)) := Ring.HasFiniteQuotients.finiteQuotient
      (Ideal.span_singleton_eq_bot.not.mpr (u i).property.1)
    have hNupos : (0:ℝ)<(Ideal.span {(u i).val}:Ideal O).absNorm := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (u i).property.1))
    apply (div_le_one (mul_pos hCcond hNupos)).mpr
    exact (hCu i).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast FiniteConductor.absNorm_le_of_le (Ideal.le_radical (I := (Ideal.span {(u i).val}:Ideal O)))) hCcond.le)
  have hms (i : κ) := hmass S hS firsteps hfirst η (u i) T hT hdis hη W Yp hYp hWS hWB x z
    alpha eps (delta/2) Ccond (Cu i) halpha halpha1 heps heps1 hx hz hrho hrho1 hline hleft hmargin
      hCcond (hCu0 i) (hCu i)
  have hmassU (i : κ) : (∑'e,‖A i e‖*(N i e)^(-(1/2:ℝ))*max 1 (Lc i*N i e)^(delta/2))≤ M := by
    refine (hms i).2.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hNu i) hmassEps.le) hCmass.le)
      (Finset.prod_nonneg (fun i _=> Real.rpow_nonneg (zero_le_one.trans (hYp i)) _))
  have hmargin0 : 1+firsteps≤ x.re+1/2 := by linarith
  have hseries (i : κ) : Summable (fun e=>‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*Sp i e‖) :=
    actual_label_series_norm_summable S hS firsteps hfirst η (u i) (hrow i) T hT weight x z
      (by linarith) hz.ge hmargin0 W1 a b ha hsupp hW1 Y hY
  have hzoff (i : κ) (e : LabelPacketIndex S (u i) T) (he : ¬N i e≤ b*Y) : Sp i e=0 :=
    MellinReconstruction.polynomial_zero_of_scale_cutoff (rowCharacter S hS.prime (u i)) W1 a b Y
      (N i e) hsupp hY (hNp i e) (lt_of_not_ge he)
  have hupp (i : κ) (e : LabelPacketIndex S (u i) T) (he : N i e≤ b*Y) :
      max 1 (Lc i*N i e)≤ U^((n:ℝ)*xi) :=
    active_dilation_upper U xi (Lc i) (N i e) b Y n hU hxi (hLM i) (hNp i e).le he hcut
  have hb := packet_weighted_bins plane (fun i=> labelPacketBase S (u i) T Pbase) A Sp N hNp Lc d U xi ann n
    (fun i e=> N i e≤ b*Y) Q P R q L delta loss momentEps Ccount Cmoment M hd hM hU hxi hann hc hm
    hq hqdelta hcard hzoff hupp hseries (fun i=>(hms i).1) hmassU hselected hfull hselection
  have heq : (∑i,‖labelPolynomialPacket S hS η (u i) T hT W Yp x z W1 Y*P i‖) =
      Y^(-(1/2:ℝ))*(∑i,‖(∑'e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*Sp i e)*P i‖) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold labelPolynomialPacket
    rw [mul_assoc,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hY]
    rw [show (-(1/2:ℂ)).re=-(1/2:ℝ) by norm_num]
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le _)).trans_eq (by dsimp only [M]; ring)


end OAI.SevenEighths.Target830.Physical.Packet

#print axioms OAI.SevenEighths.Target830.Physical.Packet.actual_label_packet_bin_bound
end

/- Original module: Candidate.Target830.Physical.Public. -/
section

noncomputable section
set_option autoImplicit false

namespace OAI.SevenEighths.Target830.Physical

/-- The original positive physical slot dictionary is fine enough after every
allowed row-scale rescaling. No total-width or cardinality loss is added. -/
theorem rescaled_slot_mesh {n : ℕ} (lengths : Fin n → ℝ) (mesh d : ℝ)
    (hd : (1 / 200 : ℝ) ≤ d) (hmesh : 0 ≤ mesh)
    (hfine : ∀ j, lengths j ≤ mesh / 200) :
    ∀ j, lengths j / d ≤ mesh := by
  have hp : 0 < d := by linarith
  intro j
  apply (div_le_iff₀ hp).mpr
  have hm := mul_le_mul_of_nonneg_left hd hmesh
  linarith [hfine j]

theorem source_slot_power (Z d width : ℝ) (hZ : 0 < Z) (hd : d ≠ 0) :
    (Z ^ d) ^ (width / d) = Z ^ width := by
  rw [← Real.rpow_mul hZ.le, mul_div_cancel₀ width hd]

end OAI.SevenEighths.Target830.Physical

#print axioms OAI.SevenEighths.Target830.Physical.affine_active_box_fourth
#print axioms OAI.SevenEighths.Target830.Physical.Packet.actual_label_packet_bin_bound
#print axioms OAI.SevenEighths.Target830.Physical.scheduled_whole_slots
#print axioms OAI.SevenEighths.Target830.Physical.rescaled_slot_mesh
end

/- Original module: Candidate.Target830.Physical.SourceParameters. -/
section
/- Actual Target830 source specialization; predecessor OpenAI/Hailey Collet attribution retained. Apache-2.0. -/

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Filter
namespace OAI.SevenEighths.Target830.Physical.Source
open OAI.SevenEighths.Target830
open OAI OAI.SevenEighths OAI.SevenEighths.Target830.Physical HeckeFamily

lemma source_packet_lines (D : BaselineData) (a : ℝ)
    (ha : (51/100:ℝ)≤ a) (hatop : a≤7/8) :
    0≤(2*a-1)/2 ∧ (2*a-1)/2≤1 ∧
    1-a-6*D.e≤1/2-(2*a-1)/2 ∧
    -(1/100:ℝ)≤1/2-(2*a-1)/2 ∧
    1+4*D.e≤(a+16*D.e)+(1/2-(2*a-1)/2) := by
  have he:=D.e_pos
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> linarith

lemma source_complex_profile_norm (D : BaselineData) (F : BaselineSourceData D) (r : ℝ) :
    ‖F.W r‖≤1 := by
  rw [F.complex_eq,Complex.norm_real,Real.norm_of_nonneg (F.bounded r).1]
  exact (F.bounded r).2

lemma source_cutoff_le_base (b : ℝ) (hb : 0≤ b) :
    ∀ᶠU:ℝ in atTop,1< U ∧ ∀d:ℝ,(1/2:ℝ)≤ d → b*U^(y/d)≤ U := by
  have he : ∀ᶠU:ℝ in atTop,b≤ U^(1/20:ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/20)).eventually (eventually_ge_atTop _)
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro d hd
  have hdp : 0< d:=by linarith
  have hy : y/d≤19/20 := by
    apply (div_le_iff₀ hdp).mpr
    have hy : y≤19/40:=by norm_num [y,h,ell,theta]
    linarith
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ) := mul_le_mul he
      (Real.rpow_le_rpow_of_exponent_le hU.le hy) (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U := by rw [←Real.rpow_add (zero_lt_one.trans hU)];norm_num
end OAI.SevenEighths.Target830.Physical.Source

#print axioms OAI.SevenEighths.Target830.Physical.Source.source_packet_lines
#print axioms OAI.SevenEighths.Target830.Physical.Source.source_complex_profile_norm
#print axioms OAI.SevenEighths.Target830.Physical.Source.source_cutoff_le_base
end
