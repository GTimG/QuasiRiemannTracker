/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed positive row fee and conductor extension 1/10^22.
The support padding is half the extension; the later budget is reduced accordingly.
Inherited notices and source attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Fixed HIGH row fee 1/10^12, source reserve half that fee.
Contour extension 1/10^10 and support padding 5/10^11 are unchanged.
Inherited notices and preceding adapter attribution follow unchanged. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-22.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module PhysicalDirect.OldPacket (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Actual old-band physical reconstruction on new geometry, adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.Schedule
import Candidate.Local.Qrh.JointDetector.BoundaryPhysical.PhysicalDirect.OldPublic
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.ActualBin
import Submissions.hailey_collet_1252270103.Cycle25.Numerator.BoxReconstruction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped BigOperators Classical ContDiff
namespace Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Qrh.JointDetector.BoundaryPhysical.Return.Geometry.BoundsN] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic OAI OAI.SevenEighths
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic
open Qrh.JointDetector.BoundaryPhysical.Return.GenericArithmetic QRH.Record12518109Count Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.OldFourth Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
local notation "O" => HeckeFamily.O
theorem old_weighted_dilation_bin {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (kap d U R q L v xi ann delta loss epsilon Ccount Cmoment : ℝ)
    (hk : 7/10 ≤ kap) (hd : d0 ≤ d ∧ d ≤ dm)
    (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta / 2) (hv : 0 ≤ v) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hcard : (s.card : ℝ) ≤ Ccount * U^R)
    (hselected : ∀ i ∈ s, U^(q*capOld kap d (v+xi+ann)-loss) ≤ ‖Q i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^(q*L))
    (henergy : (∑ i ∈ s, ‖S i‖^4 * ‖Q i‖^2) ≤ Cmoment * U^(1+epsilon)) :
    U^(-delta*v/2) * (∑ i ∈ s, ‖S i * P i‖) ≤
      Ccount * Cmoment * U^(q*L-q*baseCapacity kap d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2-
        delta/4*(v+xi+ann)) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hh := weighted_amplitude_bin s S Q P U R (q*L)
    (q*capOld kap d (v+xi+ann)-loss) epsilon Ccount Cmoment hU0 hc hm
    hcard hselected hfull henergy
  have hdelta : 0 ≤ delta := by linarith
  have hdamp := capacity_damping (d:=d) hk (by positivity : 0 ≤ v+xi+ann) hq hqdelta
  calc
    _ ≤ U^(-delta*v/2) *
        (Ccount*Cmoment*U^(q*L-(q*capOld kap d (v+xi+ann)-loss)/2+(3*R+1+epsilon)/4)) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hU0.le _)
    _ = (Ccount*Cmoment) * (U^(-delta*v/2) *
        U^(q*L-(q*capOld kap d (v+xi+ann)-loss)/2+(3*R+1+epsilon)/4)) := by ring
    _ = Ccount*Cmoment*U^(-delta*v/2+q*L-
        (q*capOld kap d (v+xi+ann)-loss)/2+(3*R+1+epsilon)/4) := by
      rw [←Real.rpow_add hU0]
      congr 1
      congr 1
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by have hc0 := le_trans zero_le_one hc; have hm0 := le_trans zero_le_one hm; positivity)
      apply Real.rpow_le_rpow_of_exponent_le hU
      linarith



theorem finite_old_weighted_dilation_bins {ι : Type*} (s : Finset ι) (n : ℕ)
    (S Q : ℕ → ι → ℂ) (P f : ι → ℂ)
    (kap d U R q L xi ann delta loss epsilon Ccount Cmoment M : ℝ)
    (hk : 7/10 ≤ kap) (hd : d0 ≤ d ∧ d ≤ dm)
    (hU : 1 ≤ U) (hc : 1 ≤ Ccount) (hm : 1 ≤ Cmoment) (hM : 0 ≤ M)
    (hq : 0 ≤ q) (hqdelta : q ≤ delta/2) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
    (hcard : (s.card : ℝ) ≤ Ccount*U^R)
    (hsplit : ∀ i ∈ s, f i = ∑ j ∈ Finset.range (n+1),
      ((M * U^(-delta*((j : ℝ)*xi)/2) : ℝ) : ℂ) * S j i)
    (hselected : ∀ j ∈ Finset.range (n+1), ∀ i ∈ s,
      U^(q*capOld kap d ((j : ℝ)*xi+xi+ann)-loss) ≤ ‖Q j i‖)
    (hfull : ∀ i ∈ s, ‖P i‖ ≤ U^(q*L))
    (henergy : ∀ j ∈ Finset.range (n+1),
      (∑ i ∈ s, ‖S j i‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i ∈ s, ‖f i * P i‖) ≤
      ((n+1 : ℕ) : ℝ)*M*Ccount*Cmoment*
        U^(q*L-q*baseCapacity kap d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hdelta : 0 ≤ delta := by linarith
  let E : ℝ := q*L-q*baseCapacity kap d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2
  have hj (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∑ i ∈ s, ‖(((M * U^(-delta*((j : ℝ)*xi)/2) : ℝ) : ℂ) * S j i) * P i‖) ≤
      M*Ccount*Cmoment*U^E := by
    have hb := old_weighted_dilation_bin s (S j) (Q j) P kap d U R q L ((j : ℝ)*xi) xi ann delta
      loss epsilon Ccount Cmoment hk hd hU hc hm hq hqdelta (mul_nonneg (Nat.cast_nonneg _) hxi)
      hxi hann hcard (hselected j hj) hfull (henergy j hj)
    have hpow : U^(E-delta/4*((j : ℝ)*xi+xi+ann)) ≤ U^E :=
      Real.rpow_le_rpow_of_exponent_le hU (by
        have hv : 0 ≤ (j : ℝ)*xi+xi+ann := by positivity
        have := mul_nonneg hdelta hv
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
      _ ≤ M * (Ccount*Cmoment*U^(E-delta/4*((j : ℝ)*xi+xi+ann))) :=
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


variable {ι : Type*} [Fintype ι] {α : ι → Type*}

theorem old_packet_weighted_bins
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (Lc : ι → ℝ) (kap d U xi ann : ℝ) (n : ℕ)
    (valid : ∀ i, α i → Prop) [∀ i e, Decidable (valid i e)]
    (Q : ℕ → ι → ℂ) (P : ι → ℂ)
    (R q L delta loss epsilon Ccount Cmoment M : ℝ)
    (hk : 7/10 ≤ kap) (hd : d0 ≤ d ∧ d ≤ dm) (hM : 0 < M) (hU : 1 ≤ U) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
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
      U^(q*capOld kap d ((j : ℝ)*xi+xi+ann)-loss) ≤ ‖Q j i‖)
    (hfull : ∀ i, ‖P i‖ ≤ U^(q*L))
    (hselection : ∀ j ∈ Finset.range (n+1), ∀ e : ∀ i, α i,
      (∑ i, ‖if valid i (e i) ∧ dilationBox U xi n (max 1 (Lc i*N i (e i))) = j
        then S i (e i) else 0‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon)) :
    (∑ i, ‖(∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)*P i‖) ≤
      ((n+1 : ℕ) : ℝ)*M*Ccount*Cmoment*
        U^(q*L-q*baseCapacity kap d/2+(3*R+1+epsilon)/4+loss/2+delta*(xi+ann)/2) := by
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hrho : 0 ≤ delta/2 := by linarith
  let B (j : ℕ) (i : ι) := normalizedBox U xi n j (delta/2) M
    (fun e=>max 1 (Lc i*N i e)) (fun e=>A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e)
  have hsplit (i : ι) : (∑' e,A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) =
      ∑ j ∈ Finset.range (n+1), ((M*U^(-delta*((j : ℝ)*xi)/2) : ℝ):ℂ)*B j i := by
    have hh := normalized_box_reconstruction U xi n (delta/2) M hU0 hM.ne'
      (fun e=>max 1 (Lc i*N i e)) (fun e=>A i e*(N i e:ℂ)^(-(1/2:ℂ))*S i e) (hseries i)
    have hexp (j : ℕ) : -(delta/2)*((j : ℝ)*xi) = -delta*((j : ℝ)*xi)/2 := by ring
    simpa only [hexp, B] using hh
  have henergy (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∑ i, ‖B j i‖^4 * ‖Q j i‖^2) ≤ Cmoment*U^(1+epsilon) :=
    normalized_dilation_box_fourth base A S N hN Lc (delta/2) U xi n j valid (Q j) M
      (Cmoment*U^(1+epsilon)) hM hU hxi hrho hzero hupper hs hmass (hselection j hj)
  exact finite_old_weighted_dilation_bins Finset.univ n B Q P _ kap d U R q L xi ann delta loss epsilon
    Ccount Cmoment M hk hd hU hc hm hM.le hq hqdelta hxi hann (by simpa using hcard)
    (fun i hi=>hsplit i) (fun j hj i hi=>hselected j hj i) (fun i hi=>hfull i) henergy



theorem old_actual_label_packet_bin_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (massEps cp bProfile Bp : ℝ) (hmassEps : 0 < massEps)
    (hcp : 0 < cp) (hdp : 0 < bProfile) (hBp : 0 ≤ Bp) :
    ∃ Cmass : ℝ, 0 < Cmass ∧ ∀
      (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character)
      (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
      (hdis : ∀P:∀i,T i,Function.Injective (fun i=>(P i).val))
      (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
      (Pbase : ∀i,T i) (W : ι→ℝ→ℂ) (Yp : ι→ℝ),
      (∀i,1≤ Yp i) → (∀i,Function.support (W i)⊆Set.Icc cp bProfile) →
      (∀i y,‖W i y‖≤ Bp) → ∀(x z : ℂ) (alpha eps : ℝ),
      51/100≤ alpha → alpha≤1 → 0< eps → eps≤1/1000 →
      x.re=alpha+16*eps → z.re=17/50 →
      ∀(κ : Type) [Fintype κ] (u : κ→FreeRow)
      (W1 : ℝ→ℂ) (a b Y : ℝ), 0< a → Function.support W1⊆Set.Icc a b →
      ContDiff ℝ ∞ W1 → 0< Y →
      ∀(kap d U xi ann : ℝ) (n : ℕ) (Cu : κ→ℝ) (Ccond : ℝ)
      (Q : ℕ→κ→ℂ) (P : κ→ℂ)
      (R q L delta loss momentEps Ccount Cmoment : ℝ),
      7/10≤ kap → d0≤ d ∧ d≤ dm → 1≤ U → 0≤ xi → 0≤ ann → 1≤ Ccount → 1≤ Cmoment → 0≤ q → q≤ delta/2 →
      0≤ delta/2 → delta/2≤1 →
      1-alpha-6*eps≤1/2-delta/2 → -(1/100:ℝ)≤1/2-delta/2 →
      1+firsteps≤ x.re+(1/2-delta/2) → 0< Ccond →
      (∀i,0≤ Cu i) → (∀i,Cu i≤ Ccond*((Ideal.span {(u i).val}:Ideal O).radical.absNorm:ℝ)) →
      (∀i,((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ)≤ U) →
      (∀i,(rowCharacter S hS.prime (u i)).residue≠1) →
      b*Y≤ U^((n:ℝ)*xi) →
      (Fintype.card κ:ℝ)≤ Ccount*U^R →
      (∀j∈Finset.range (n+1),∀i,U^(q*capOld kap d ((j:ℝ)*xi+xi+ann)-loss)≤‖Q j i‖) →
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
          Ccount*Cmoment*U^(q*L-q*baseCapacity kap d/2+(3*R+1+momentEps)/4+loss/2+delta*(xi+ann)/2) := by
  obtain ⟨Cmass,hCmass,hmass⟩ := actual_physical_label_mass (ι:=ι) massEps cp bProfile Bp hmassEps hcp hdp hBp
  refine ⟨Cmass,hCmass,?_⟩
  intro S hS firsteps hfirst η T hT hdis hη Pbase W Yp hYp hWS hWB x z alpha eps
    halpha halpha1 heps heps1 hx hz κ _ u W1 a b Y ha hsupp hW1 hY kap d U xi ann n Cu Ccond Q P
    R q L delta loss momentEps Ccount Cmoment hk hd hU hxi hann hc hm hq hqdelta hrho hrho1
    hline hleft hmargin hCcond hCu0 hCu hNu hrow hcut hcard hselected hfull Lc hselection
  let weight : ∀i,T i→ℂ := fun i P=>physicalSlotWeight P.val (W i) (Yp i) z
  let A (i : κ) := labelPacketCoefficient S hS η (u i) T hT weight x z
  let N (i : κ) (e : LabelPacketIndex S (u i) T) : ℝ := labelPacketScale S (u i) T e
  let Sp (i : κ) (e : LabelPacketIndex S (u i) T) :=
    HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1 (Y/N i e) 0 0
  let M : ℝ := Cmass*U^massEps*∏i,(Yp i)^(-(4/25:ℝ))
  have hU0 : 0< U := lt_of_lt_of_le zero_lt_one hU
  have hNp (i : κ) (e : LabelPacketIndex S (u i) T) : 0< N i e :=
    lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S (u i) T e)
  have hM : 0< M := mul_pos (mul_pos hCmass (Real.rpow_pos_of_pos hU0 _))
    (Finset.prod_pos (fun i _=>Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (hYp i)) _))
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
      (Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (zero_le_one.trans (hYp i)) _))
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
  have hb := old_packet_weighted_bins (fun i=>labelPacketBase S (u i) T Pbase) A Sp N hNp Lc kap d U xi ann n
    (fun i e=>N i e≤ b*Y) Q P R q L delta loss momentEps Ccount Cmoment M hk hd hM hU hxi hann hc hm
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



end Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect.Source
