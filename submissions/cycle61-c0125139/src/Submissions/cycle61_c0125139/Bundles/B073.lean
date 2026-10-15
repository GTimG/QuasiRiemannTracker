/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B047
import Submissions.cycle61_c0125139.Bundles.B056
import Submissions.cycle61_c0125139.Bundles.B057
import Submissions.cycle61_c0125139.Bundles.B058
import Submissions.cycle61_c0125139.Bundles.B067
import Submissions.cycle61_c0125139.Bundles.B069
import Submissions.cycle61_c0125139.Bundles.B071
import Submissions.cycle61_c0125139.Bundles.B072

/- BEGIN ORIGINAL Cycle61.Numerator.Source.OldPacket; sha256 9b5c47eb07bc0662bd4a2c2f2fe19cd1921c1b1016eddb2617348586d520581f -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                         
                                  
                                          
noncomputable section
set_option maxHeartbeats 2400000
open scoped BigOperators Classical ContDiff
namespace Cycle61.Numerator.Source
open Cycle61.Arithmetic Cycle61.Numerator.OldFourth Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
local notation "O" => HeckeFamily.O
theorem old_weighted_dilation_bin {ι : Type*} (s : Finset ι) (S Q P : ι → ℂ)
    (kap d U R q L v xi ann delta loss epsilon Ccount Cmoment : ℝ)
    (hk : 7/10 ≤ kap) (hd : d0 ≤ d ∧ d ≤ dMinus)
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
    (hk : 7/10 ≤ kap) (hd : d0 ≤ d ∧ d ≤ dMinus)
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
    (hk : 7/10 ≤ kap) (hd : d0 ≤ d ∧ d ≤ dMinus) (hM : 0 < M) (hU : 1 ≤ U) (hxi : 0 ≤ xi) (hann : 0 ≤ ann)
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
    (massEps cp dp Bp : ℝ) (hmassEps : 0 < massEps)
    (hcp : 0 < cp) (hdp : 0 < dp) (hBp : 0 ≤ Bp) :
    ∃ Cmass : ℝ, 0 < Cmass ∧ ∀
      (S : Finset (Ideal O)) (hS : SourceExclusions S)
      (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character)
      (T : ι→Finset ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
      (hdis : ∀P:∀i,T i,Function.Injective (fun i=>(P i).val))
      (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
      (Pbase : ∀i,T i) (W : ι→ℝ→ℂ) (Yp : ι→ℝ),
      (∀i,1≤Yp i) → (∀i,Function.support (W i)⊆Set.Icc cp dp) →
      (∀i y,‖W i y‖≤Bp) → ∀(x z : ℂ) (alpha eps : ℝ),
      51/100≤alpha → alpha≤1 → 0<eps → eps≤1/1000 →
      x.re=alpha+16*eps → z.re=17/50 →
      ∀(κ : Type) [Fintype κ] (u : κ→FreeRow)
      (W1 : ℝ→ℂ) (a b Y : ℝ), 0<a → Function.support W1⊆Set.Icc a b →
      ContDiff ℝ ∞ W1 → 0<Y →
      ∀(kap d U xi ann : ℝ) (n : ℕ) (Cu : κ→ℝ) (Ccond : ℝ)
      (Q : ℕ→κ→ℂ) (P : κ→ℂ)
      (R q L delta loss momentEps Ccount Cmoment : ℝ),
      7/10≤kap → d0≤d ∧ d≤dMinus → 1≤U → 0≤xi → 0≤ann → 1≤Ccount → 1≤Cmoment → 0≤q → q≤delta/2 →
      0≤delta/2 → delta/2≤1 →
      1-alpha-6*eps≤1/2-delta/2 → -(1/100:ℝ)≤1/2-delta/2 →
      1+firsteps≤x.re+(1/2-delta/2) → 0<Ccond →
      (∀i,0≤Cu i) → (∀i,Cu i≤Ccond*((Ideal.span {(u i).val}:Ideal O).radical.absNorm:ℝ)) →
      (∀i,((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ)≤U) →
      (∀i,(rowCharacter S hS.prime (u i)).residue≠1) →
      b*Y≤U^((n:ℝ)*xi) →
      (Fintype.card κ:ℝ)≤Ccount*U^R →
      (∀j∈Finset.range (n+1),∀i,U^(q*capOld kap d ((j:ℝ)*xi+xi+ann)-loss)≤‖Q j i‖) →
      (∀i,‖P i‖≤U^(q*L)) →
      let Lc (i : κ) := Cu i/(Ccond*((Ideal.span {(u i).val}:Ideal O).absNorm:ℝ))
      (∀j∈Finset.range (n+1),∀e:∀i,LabelPacketIndex S (u i) T,
        (∑i,‖if (labelPacketScale S (u i) T (e i):ℝ)≤b*Y ∧
          dilationBox U xi n (max 1 (Lc i*(labelPacketScale S (u i) T (e i):ℝ)))=j
          then HeckeDyadic.polynomial (rowCharacter S hS.prime (u i)) false W1
            (Y/(labelPacketScale S (u i) T (e i):ℝ)) 0 0 else 0‖^4 * ‖Q j i‖^2)
          ≤Cmoment*U^(1+momentEps)) →
      (∑i,‖labelPolynomialPacket S hS η (u i) T hT W Yp x z W1 Y*P i‖) ≤
        Y^(-(1/2:ℝ))*((n+1:ℕ):ℝ)*(Cmass*U^massEps*∏i,(Yp i)^(-(4/25:ℝ)))*
          Ccount*Cmoment*U^(q*L-q*baseCapacity kap d/2+(3*R+1+momentEps)/4+loss/2+delta*(xi+ann)/2) := by
  obtain ⟨Cmass,hCmass,hmass⟩ := actual_physical_label_mass (ι:=ι) massEps cp dp Bp hmassEps hcp hdp hBp
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
  have hU0 : 0<U := lt_of_lt_of_le zero_lt_one hU
  have hNp (i : κ) (e : LabelPacketIndex S (u i) T) : 0<N i e :=
    lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le S (u i) T e)
  have hM : 0<M := mul_pos (mul_pos hCmass (Real.rpow_pos_of_pos hU0 _))
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
  have hmassU (i : κ) : (∑'e,‖A i e‖*(N i e)^(-(1/2:ℝ))*max 1 (Lc i*N i e)^(delta/2))≤M := by
    refine (hms i).2.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hNu i) hmassEps.le) hCmass.le)
      (Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (zero_le_one.trans (hYp i)) _))
  have hmargin0 : 1+firsteps≤x.re+1/2 := by linarith
  have hseries (i : κ) : Summable (fun e=>‖A i e*(N i e:ℂ)^(-(1/2:ℂ))*Sp i e‖) :=
    actual_label_series_norm_summable S hS firsteps hfirst η (u i) (hrow i) T hT weight x z
      (by linarith) hz.ge hmargin0 W1 a b ha hsupp hW1 Y hY
  have hzoff (i : κ) (e : LabelPacketIndex S (u i) T) (he : ¬N i e≤b*Y) : Sp i e=0 :=
    MellinReconstruction.polynomial_zero_of_scale_cutoff (rowCharacter S hS.prime (u i)) W1 a b Y
      (N i e) hsupp hY (hNp i e) (lt_of_not_ge he)
  have hupp (i : κ) (e : LabelPacketIndex S (u i) T) (he : N i e≤b*Y) :
      max 1 (Lc i*N i e)≤U^((n:ℝ)*xi) :=
    active_dilation_upper U xi (Lc i) (N i e) b Y n hU hxi (hLM i) (hNp i e).le he hcut
  have hb := old_packet_weighted_bins (fun i=>labelPacketBase S (u i) T Pbase) A Sp N hNp Lc kap d U xi ann n
    (fun i e=>N i e≤b*Y) Q P R q L delta loss momentEps Ccount Cmoment M hk hd hM hU hxi hann hc hm
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



end Cycle61.Numerator.Source

end
/- END ORIGINAL Cycle61.Numerator.Source.OldPacket -/

/- BEGIN ORIGINAL Cycle61.Numerator.Source.OldSelected; sha256 ce02bb0494dd9cdce8e208391a5f8152b78e0e1cd34be48b751aa927355c503d -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                          
                                         

/-! Actual source packet estimates with the original physical fourth moment
fully discharged. Remaining bin premises are finite count and prime-amplitude
inequalities, supplied by the certified source amplitude partition. -/
noncomputable section
set_option maxHeartbeats 2400000
open scoped BigOperators Classical ContDiff
open Filter
namespace Cycle61.Numerator.Source
open Cycle25.Weighted Cycle25.Weighted.Numerator Cycle25.Numerator
open Cycle61.Arithmetic Cycle61.Numerator.OldFourth
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open ProbeRowRadicalConductor Cycle25DetectorRowCount Cycle61DetectorCount
local notation "O" => HeckeFamily.O

lemma old_source_cutoff_le_base (b : ℝ) (hb : 0<b) :
    ∀ᶠ U:ℝ in atTop,1<U ∧ ∀d:ℝ,d0≤d → b*U^(y/d)≤U^(100:ℝ) := by
  have hev := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1)).eventually (eventually_ge_atTop b)
  filter_upwards [hev,eventually_gt_atTop (1:ℝ)] with U hbU hU
  refine ⟨hU,?_⟩
  intro d hd
  have hdpos := d0_pos.trans_le hd
  have hym : y/d≤99 := by
    apply (div_le_iff₀ hdpos).mpr
    norm_num [d0,y] at *
    linarith
  calc
    _ ≤ U^1*U^(y/d) := mul_le_mul_of_nonneg_right hbU (Real.rpow_nonneg (by linarith) _)
    _ = U^(1+y/d) := (Real.rpow_add (by linarith : 0<U) (1:ℝ) (y/d)).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)

theorem old_source_packet_selected_bin (D : BaselineData)
    (F : BaselineSourceData D) (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hkbeta : 2*HeckeZeroSupremum.beta-1≤D.momentKappa)
    (hfine : ∀j,D.length j≤Cycle25.sourceMesh D.t/200) (J : Finset (Fin D.N)) :
    ∃degree : ℕ,∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z → d0≤d → d≤dMinus → U=Z^d →
      ∀(η : Character) (x z : ℂ) (a height : ℝ), (51/100:ℝ)≤a → a≤7/8 →
      x.re=a+16*D.e → z.re=17/50 → 0≤height → |z.im|≤height →
      ∀(rows : Finset FreeRow),
      (∀u∈rows,U^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤U) →
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1) →
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val)) →
      (∀i P,P∈sourcePrimePool F Z i→IsCoprime P.val η.modulus) →
      (∀i:J,sourcePrimePool F Z i.val) →
      ∀(selected : ℕ→Finset (Fin D.N)) (P : rows→ℂ) (q R selLoss Ccount : ℝ),
      0≤q → q≤(2*a-1)/2 → 1≤Ccount → (rows.card:ℝ)≤Ccount*U^R →
      (∀i,‖P i‖≤U^(q*(Cycle61.Arithmetic.ell/d))) →
      (∀j∈Finset.range (coefficientBoxCount100 D.t+1),
        (∑s∈selected j,D.length s/d)≤ capOld D.momentKappa d ((j:ℝ)*D.t+D.t+D.t)) →
      (∀j∈Finset.range (coefficientBoxCount100 D.t+1),∀i:rows,
        U^(q*capOld D.momentKappa d ((j:ℝ)*D.t+D.t+D.t)-selLoss)≤
          ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z‖) →
      (∀j∈Finset.range (coefficientBoxCount100 D.t+1),∀i:rows,
        ‖∏s∈selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z‖≤U) →
      (∑i:rows,‖labelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
        (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(y/d))*P i‖) ≤
        C*Ccount*(1+height)^degree*(U^(y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(Cycle61.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
            (3*R+1+D.t+D.t)/4+selLoss/2+(2*a-1)*(D.t+D.t)/2) := by
  obtain ⟨Cm,hCm,hpacket⟩ := old_actual_label_packet_bin_bound (ι:=J) D.t 1 2 1 D.t_pos
    (by norm_num) (by norm_num) (by norm_num)
  have hsmall : 2*D.t+D.t≤1/2 := by have := D.t_small;linarith
  obtain ⟨degree,Cr,hCr,hmoment⟩ := baseline_old_active_box_fourth D F hbeta hkbeta F.W D.t D.t D.t 2
    D.t_pos D.t_pos D.t_pos (by norm_num) hsmall
  let Cr' : ℝ := max 1 Cr
  have hCr' : 1≤Cr' := le_max_left _ _
  let C : ℝ := ((coefficientBoxCount100 D.t+1:ℕ):ℝ)*Cm*Cr'
  have hC : 0 < C := by dsimp [C];have := zero_lt_one.trans_le hCr';positivity
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hmoment,old_source_cutoff_le_base 2 (by norm_num)] with U hmom hcutU
  dsimp only [BaselineData.toMomentData] at hmom
  refine ⟨hmom.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase selected P q R selLoss Ccount hq hqtop hCc hcard hfull hcap hselected hcrude
  have hd0 : 0 < d := d0_pos.trans_le hd
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU0 : 0 < U := zero_lt_one.trans hmom.1
  have hscale (s : Fin D.N) : U^(D.length s/d)=Z^(D.length s) := by
    rw [hUZ,←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd0.ne']
  let data (i : rows) : PhysicalReflectionData F.S F.exclusions.prime i.val :=
    Classical.choice (physical_reflection_data_exists F.S F.exclusions.prime i.val (hrow i.val i.property))
  let Cu (i : rows) := (data i).combinedConductor
  let Ccond : ℝ := fixedConductorConstant F.S
  have hCcond : 0 < Ccond := by dsimp only [Ccond];exact_mod_cast fixedConductorConstant_pos F.S F.exclusions.prime
  let Ts (s : J) := sourcePrimePool F Z s.val
  let hTs := fun s:J=>source_prime_pool_outside F Z s.val
  let Q (j : ℕ) (i : rows) := ∏s∈selected j,
    HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z
  have hQprod (j : ℕ) (i : rows) :
      (∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
        (U^(D.length s.val/d)) z) = Q j i := by
    calc
      _ = ∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (Z^(D.length s.val)) z := by
        apply Finset.prod_congr rfl
        intro s hs
        rw [hscale s.val]
      _ = _ := by
        exact Finset.prod_coe_sort (selected j)
          (fun s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2 (Z^(D.length s)) z)
  have hwpos (s : Fin D.N) : 0 < D.length s/d := div_pos (D.slots_pos s) hd0
  have hwmax (s : Fin D.N) : D.length s/d≤Cycle25.sourceMesh D.t := by
    apply (div_le_iff₀ hd0).mpr
    have ht := Cycle25.sourceMesh_pos D.t_pos
    have hs := hfine s
    have hdmin : (1/200:ℝ)≤d := hd
    nlinarith
  have hYp (s : J) : 1≤Z^(D.length s.val) := Real.one_le_rpow hZ.le (D.slots_pos s.val).le
  have hY : 0<U^(y/d) := Real.rpow_pos_of_pos hU0 _
  have hcut : 2*U^(y/d)≤U^((coefficientBoxCount100 D.t:ℝ)*D.t) := by
    apply (hcutU.2 d hd).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hmom.1.le (box100_extent D.t_pos)
  obtain ⟨hrho,hrho1,hline,hleft,hmargin⟩ := source_packet_lines D a ha hatop
  have hmomentInput (j : ℕ) (hj : j∈Finset.range (coefficientBoxCount100 D.t+1))
      (e : ∀i:rows,LabelPacketIndex F.S i.val Ts) :
      (∑i:rows,‖if (labelPacketScale F.S i.val Ts (e i):ℝ)≤2*U^(y/d) ∧
        dilationBox U D.t (coefficientBoxCount100 D.t)
          (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
            (labelPacketScale F.S i.val Ts (e i):ℝ)))=j
        then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false F.W
          (U^(y/d)/(labelPacketScale F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖Q j i‖^2) ≤
      (Cr'*(1+height)^degree)*U^(1+D.t+D.t) := by
    have hh := hmom.2 rows hrows data (fun i=>(labelPacketScale F.S i.val Ts (e i):ℝ))
      (fun i=>lt_of_lt_of_le zero_lt_one (by exact_mod_cast labelPacketScale_one_le F.S i.val Ts (e i)))
      d hd hdmax j hj (selected j) (fun s=>D.length s.val/d) (fun _=>z) height
      (fun s=>hwpos s.val) (fun s=>hwmax s.val) (fun _=>hz) hheight (fun _=>hzim)
      ((Finset.sum_coe_sort (selected j) (fun s=>D.length s/d)).le.trans (hcap j hj))
      (by
        intro i
        change ‖(∏s:selected j,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ i.val.val F.W 2
          (U^(D.length s.val/d)) z)‖≤U
        rw [hQprod]
        exact hcrude j hj i)
    have hh' : _ ≤ (Cr'*(1+height)^degree)*U^(1+D.t+D.t) := hh.trans (by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hU0.le _)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by linarith) _))
    
    convert hh' using 1
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun qq : ℂ => ‖if (labelPacketScale F.S i.val Ts (e i):ℝ)≤2*U^(y/d) ∧
      dilationBox U D.t (coefficientBoxCount100 D.t)
        (max 1 ((Cu i/(Ccond*((Ideal.span {i.val.val}:Ideal O).absNorm:ℝ)))*
          (labelPacketScale F.S i.val Ts (e i):ℝ)))=j
      then HeckeDyadic.polynomial (rowCharacter F.S F.exclusions.prime i.val) false F.W
        (U^(y/d)/(labelPacketScale F.S i.val Ts (e i):ℝ)) 0 0 else 0‖^4*‖qq‖^2) (hQprod j i).symm

  have hCM : 1≤Cr'*(1+height)^degree := one_le_mul_of_one_le_of_one_le hCr' (one_le_pow₀ (by linarith))
  have hb := hpacket F.S F.exclusions (4*D.e) F.first η Ts hTs hdis
    (fun s Q hQ=>hη s.val Q hQ) Pbase (fun _=>F.W) (fun s=>Z^(D.length s.val)) hYp
    (fun _=>F.complex_support) (fun _ y=>source_complex_profile_norm D F y) x z a D.e ha
    (by linarith) D.e_pos D.e_small.le hx hz rows Subtype.val F.W 1 2 (U^(y/d))
    (by norm_num) F.complex_support (F.W.smooth ⊤) hY D.momentKappa d U D.t D.t (coefficientBoxCount100 D.t) Cu Ccond Q P
    R q (Cycle61.Arithmetic.ell/d) (2*a-1) selLoss (D.t+D.t) Ccount
    (Cr'*(1+height)^degree) D.momentKappa_lo ⟨hd,hdmax⟩ hmom.1.le D.t_pos.le D.t_pos.le hCc hCM hq hqtop hrho hrho1 hline hleft
    (by simpa only [hx] using hmargin) hCcond (fun i=>(data i).combined_pos.le)
    (fun i=>(data i).combined_le_radical) (fun i=>(hrows i.val i.property).2)
    (fun i=>hrow i.val i.property) hcut (by simpa using hcard) hselected hfull (by simpa only [add_assoc] using hmomentInput)
  apply hb.trans_eq
  dsimp only [C]
  have hp : U^(D.t+q*(Cycle61.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
      (3*R+1+D.t+D.t)/4+selLoss/2+(2*a-1)*(D.t+D.t)/2) =
      U^D.t*U^(q*(Cycle61.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
      (3*R+1+D.t+D.t)/4+selLoss/2+(2*a-1)*(D.t+D.t)/2) := by
    rw [←Real.rpow_add hU0]
    congr 1
    ring
  rw [hp]
  ring

end Cycle61.Numerator.Source

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. Variable moment parameter, genuine physical source. -/

end
/- END ORIGINAL Cycle61.Numerator.Source.OldSelected -/

/- BEGIN ORIGINAL Cycle61.Numerator.Source.OldClass; sha256 86fb90e5de7a89e028a5885351fd0c3bc87005f9f15dee680c974a6d7f68a036 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                           
                                        

noncomputable section
open scoped Classical BigOperators
open Filter
namespace Cycle61.Numerator.Source
open Cycle61.Arithmetic Cycle61.Numerator.OldFourth
open Cycle25.Numerator
open OAI OAI.SevenEighths Cycle61DetectorCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorFiberPartition ProbeHighRowFamily Cycle25ProbeFinalAssembly Cycle25DetectorRowCount
open ProbePhysical HeckeFamily HeckeInverseAmplification

lemma old_whole_slots (D : BaselineData)
    (hfine : ∀j,D.length j ≤ Cycle25.sourceMesh D.t/200)
    (d v delta : ℝ) (hd : d0 ≤ d ∧ d ≤ dMinus) (hv : 0 ≤ v) (hdelta : 0 ≤ delta)
    (main : Finset (Fin D.N)) (g : Fin D.N → ℝ)
    (hg : ∀j,0 ≤ g j ∧ g j ≤ delta/2) (herror : ∀j,j ∉ main → g j=0) :
    let widths := fun j=>D.length j/d
    let q := weightedMean Finset.univ widths g
    q=(∑j,widths j*g j)/(ell/d) ∧ 0 ≤ q ∧ q ≤ delta/2 ∧
    ∃selected : Finset (Fin D.N),selected ⊆ main ∧ (∀j∈selected,0<g j) ∧
      (∑j∈selected,widths j) ≤ capOld D.momentKappa d v ∧
      q*capOld D.momentKappa d v-(delta/2)*Cycle25.sourceMesh D.t ≤ ∑j∈selected,widths j*g j ∧
      q*capOld D.momentKappa d v-(delta/2)*Cycle25.sourceMesh D.t ≤ ∑j∈selected,widths j*g j ∧
      ∀U:ℝ,1 ≤ U → ∀Q:Fin D.N → ℂ,
        (∀j,0<g j → U^(2*widths j*g j) ≤ ‖Q j‖^2) → 
        U^(2*q*capOld D.momentKappa d v-delta*Cycle25.sourceMesh D.t) ≤ ‖∏j∈selected,Q j‖^2 := by
  have hdp:=d0_pos.trans_le hd.1
  let widths:=fun j=>D.length j/d
  have hsum:(∑j,widths j)=ell/d:=by dsimp [widths];rw [←Finset.sum_div,D.slots_sum]
  have hL:0<∑j,widths j:=by rw [hsum];exact div_pos ell_pos hdp
  have hw (j:Fin D.N):0 ≤ widths j:=(div_pos (D.slots_pos j) hdp).le
  have hm:=Cycle25.sourceMesh_pos D.t_pos
  have hwm (j:Fin D.N):widths j ≤ Cycle25.sourceMesh D.t :=
    Cycle61.Numerator.Fourth.rescaled_slot_mesh D (Cycle25.sourceMesh D.t) d
      hd.1 hfine j
  have hcap:capOld D.momentKappa d v ≤ ∑j,widths j:=by rw [hsum];exact capOld_le_supply D.momentKappa_lo hd hv
  obtain ⟨hq,hqtop⟩:=weightedMean_bounds Finset.univ widths g delta (fun j _=>hw j) hL (fun j _=>hg j)
  obtain ⟨T,_,hT,hTpos,hTcap,hgain,hspike⟩:=SlotSelection.zero_error_whole_slots
    Finset.univ main widths g delta (Cycle25.sourceMesh D.t) (capOld D.momentKappa d v)
    hdelta hm.le (fun j _=>hw j) (fun j _=>hwm j) hL (fun j _=>hg j)
    (fun j _=>herror j) (capOld_nonneg D.momentKappa d v) hcap
  refine ⟨?_,hq,hqtop,T,hT,hTpos,hTcap,hgain,hgain,?_⟩
  · unfold weightedMean;rw [hsum]
  · intro U hU Q hQ;exact hspike U hU Q (fun j _=>hQ j)

theorem old_source_class_main_selection (D : BaselineData)
    (F : BaselineSourceData D)
    (hfine : ∀j,D.length j  ≤  Cycle25.sourceMesh D.t/200)
    (Z d v δ : ℝ) (hZ : 1 < Z) (hd : d0  ≤  d ∧ d  ≤  dMinus) (hv : 0  ≤  v) (hδ : 0  ≤  δ)
    (z : ℂ) (rows : Finset FreeRow) (main : Finset (Fin D.N))
    (bin : BinLabel (Finset.univ : Finset (Fin D.N)) (δ/2) D.t)
    (hne : (amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.length j/d)
      (fun u j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z) bin).Nonempty) :
    let Q := fun (u : FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z
    let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
    let g := binValue Finset.univ (δ/2) D.t bin
    let q := weightedMean Finset.univ (fun j=>D.length j/d) (maskedGain main g)
    0  ≤  q ∧ q  ≤  δ/2 ∧ ∃selected : Finset (Fin D.N),selected ⊆ main ∧
      (∑j∈selected,D.length j/d)  ≤  capOld D.momentKappa d v ∧
      ∀u∈rows',
        (Z^d)^(2*q*capOld D.momentKappa d v-
          δ*Cycle25.sourceMesh D.t)  ≤  ‖∏j∈selected,Q u j‖^2 ∧
        ((∀j,‖Q u j‖  ≤  (Z^(D.length j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q u j)+D.t))  → 
          ‖∏j∈main,Q u j‖  ≤  (Z^d)^(q*(Cycle61.Arithmetic.ell/d)+D.t*(Cycle61.Arithmetic.ell/d))) := by
  dsimp only
  let Q := fun (u : FreeRow) j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) (δ/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
  let g := binValue Finset.univ (δ/2) D.t bin
  have hdpos : 0 < d := d0_pos.trans_le hd.1
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hU : 1 < Z^d := Real.one_lt_rpow hZ hdpos
  have hscale (j : Fin D.N) : (Z^d)^(D.length j/d)=Z^(D.length j) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hgfull : ∀j,0  ≤  g j ∧ g j  ≤  δ/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j
    have he := amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=>D.length j/d) Q bin u hu j (Finset.mem_univ j)
    dsimp only [g]
    rw [←he]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  have hg : ∀j,0  ≤  maskedGain main g j ∧ maskedGain main g j  ≤  δ/2 := by
    intro j
    unfold maskedGain
    split_ifs
    · exact hgfull j
    · exact ⟨le_rfl,by positivity⟩
  obtain ⟨hqeq,hq0,hqtop,T,hT,hTpos,hTcap,hgain,hgain',hspike⟩ :=
    old_whole_slots D hfine d v δ hd hv hδ main
      (maskedGain main g) hg (fun j hj=>by simp [maskedGain,hj])
  refine ⟨hq0,hqtop,T,hT,hTcap,?_⟩
  intro u hu
  have hgrow (j : Fin D.N) : HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q u j)=g j := by
    have he := amplitude_class_value rows Finset.univ (Z^d) (δ/2) D.t D.t_pos
      (fun j=>D.length j/d) Q bin u hu j (Finset.mem_univ j)
    simpa only [hscale] using he
  refine ⟨?_,?_⟩
  · apply hspike (Z^d) hU.le (Q u)
    intro j hj
    have hjmain : j∈main := by
      by_contra hm
      simp only [maskedGain,ite_eq_right hm,lt_self_iff_false] at hj
    have hgm : maskedGain main g j=g j := by simp [maskedGain,hjmain]
    have hpos : 0 < HeckePrimeAmplitudeBins.amplitude ((Z^d)^(D.length j/d)) (δ/2) D.t (Q u j) := by
      rw [hscale,hgrow]
      rwa [hgm] at hj
    have hh := HeckePrimeAmplitudeBins.squared_spike (Z^d) (D.length j/d) (δ/2) D.t
      (Q u j) hU (div_pos (D.slots_pos j) hdpos) D.t_pos hpos
    simpa only [hscale,hgrow,hgm] using hh
  · intro hupper
    have hL : (∑j,D.length j/d)=ell/d := by rw [←Finset.sum_div,D.slots_sum]
    have hh := masked_main_product_upper main (fun j=>D.length j/d) g (Z^d) D.t (Q u)
      hU.le D.t_pos.le (fun j=>(div_pos (D.slots_pos j) hdpos).le)
      (by rw [hL];exact div_pos Cycle61.Arithmetic.ell_pos hdpos) (by
        intro j hj
        calc
          _  ≤  (Z^(D.length j))^(g j+D.t) := by
            have he := hupper j
            change ‖Q u j‖  ≤  (Z^(D.length j))^(HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q u j)+D.t) at he
            rwa [hgrow] at he
          _ = _ := by rw [←hscale j,←Real.rpow_mul (by positivity)])
    simpa only [hL] using hh


theorem old_source_selected_product_crude (D : BaselineData)
    (Z d v δ : ℝ) (hZ : 1<Z) (hd : d0≤d ∧ d≤dMinus) (hv : 0≤v)
    (hδ : 0≤δ) (hδtop : δ≤3/4)
    (selected : Finset (Fin D.N)) (Q : Fin D.N→ℂ)
    (hcap : (∑j∈selected,D.length j/d)≤capOld D.momentKappa d v)
    (hQ : ∀j,‖Q j‖≤(Z^(D.length j))^
      (HeckePrimeAmplitudeBins.amplitude (Z^(D.length j)) (δ/2) D.t (Q j)+D.t)) :
    ‖∏j∈selected,Q j‖≤Z^d := by
  have hdp := d0_pos.trans_le hd.1
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hk : 0<D.momentKappa := by linarith [D.momentKappa_lo]
  have hc : capOld D.momentKappa d v≤1 := by
    unfold capOld
    apply max_le (by norm_num)
    apply (div_le_iff₀ (by positivity : 0<6*D.momentKappa)).mpr
    linarith [min_le_left (1:ℝ) (2*y/d-1),D.momentKappa_lo]
  have hsum : (∑j∈selected,D.length j)≤d := by
    rw [←Finset.sum_div] at hcap
    exact (div_le_one hdp).mp (hcap.trans hc)
  calc
    _ ≤ ∏j∈selected,Z^(D.length j*(δ/2+D.t)) := by
      rw [norm_prod]
      apply Finset.prod_le_prod₀ (fun j _=>norm_nonneg _)
      intro j hj
      apply (hQ j).trans
      rw [←Real.rpow_mul hZ0.le]
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      apply mul_le_mul_of_nonneg_left _ (D.slots_pos j).le
      have ha := (HeckePrimeAmplitudeBins.amplitude_bounds (Z^(D.length j)) (δ/2) D.t (Q j) (by positivity)).2
      linarith
    _ = Z^((∑j∈selected,D.length j)*(δ/2+D.t)) := by
      rw [←Real.rpow_sum_of_pos hZ0,←Finset.sum_mul]
    _ ≤ Z^d := by
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      have hm := mul_le_mul_of_nonneg_right hsum (by linarith [D.t_pos] : 0≤δ/2+D.t)
      have he : δ/2+D.t≤1 := by linarith [D.t_small]
      nlinarith

/-- Fully selected actual amplitude-class packet estimate. The remaining count
premise concerns the original full class, while error slots have zero gain only
in the mean used for prime selection. -/
theorem old_source_packet_amplitude_class (D:BaselineData)
    (F:BaselineSourceData D) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hkbeta : 2*HeckeZeroSupremum.beta-1 ≤ D.momentKappa)
    (hfine:∀j,D.length j ≤ Cycle25.sourceMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,
      1<U ∧ ∀(Z d:ℝ),1<Z  →  d0 ≤ d  →  d ≤ dMinus  →  U=Z^d  → 
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ) ≤ a  →  a ≤ 7/8  → 
      x.re=a+16*D.e  →  z.re=17/50  →  0 ≤ height  →  |z.im| ≤ height  → 
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U)  → 
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)  → 
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val))  → 
      (∀i P,P∈sourcePrimePool F Z i → IsCoprime P.val η.modulus)  → 
      (∀i:J,sourcePrimePool F Z i.val)  → 
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=>D.length s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty  →  ∀R Ccount:ℝ,1 ≤ Ccount  →  (rows'.card:ℝ) ≤ Ccount*U^R  → 
      (∀u∈rows',∀s,‖Q u s‖ ≤ (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
      (∑i:rows',‖labelPolynomialPacket F.S F.exclusions η i.val
        (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
        (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(y/d))*(∏s∈main,Q i.val s)‖)  ≤ 
        C*Ccount*(1+height)^degree*(U^(y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
          U^(D.t+q*(Cycle61.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
            (3*R+1+D.t+D.t)/4+(2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Cycle61.Arithmetic.ell/d)) := by
  obtain ⟨degree,C,hC,hbin⟩ := old_source_packet_selected_bin D F hbeta hkbeta hfine J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hbin] with U hbin
  refine ⟨hbin.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow hdis hη Pbase bin
  dsimp only
  let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
  let main := (Finset.univ:Finset (Fin D.N)) \ J
  let q := weightedMean Finset.univ (fun s=>D.length s/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
  intro hne R Ccount hCc hcard hupper
  have hδ : 0 ≤ 2*a-1 := by linarith
  have hδtop : 2*a-1 ≤ 3/4 := by linarith
  have hU0 : 0<U := zero_lt_one.trans hbin.1
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have ht : 0 < D.t := D.t_pos
  have hselection (j:ℕ) := old_source_class_main_selection D F hfine Z d ((j:ℝ)*D.t+D.t+D.t) (2*a-1)
    hZ ⟨hd,hdmax⟩ (by positivity) hδ z rows main bin hne
  have hq0 : 0 ≤ q := (hselection 0).1
  have hqtop : q ≤ (2*a-1)/2 := (hselection 0).2.1
  have hchoices (j:ℕ) : ∃selected:Finset (Fin D.N),selected ⊆ main ∧
      (∑s∈selected,D.length s/d) ≤ capOld D.momentKappa d ((j:ℝ)*D.t+D.t+D.t) ∧
      ∀u∈rows',
        (Z^d)^(2*q*capOld D.momentKappa d ((j:ℝ)*D.t+D.t+D.t)-
          (2*a-1)*Cycle25.sourceMesh D.t) ≤ ‖∏s∈selected,Q u s‖^2 ∧
        ((∀s,‖Q u s‖ ≤ (Z^(D.length s))^
          (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
          ‖∏s∈main,Q u s‖ ≤ (Z^d)^(q*(Cycle61.Arithmetic.ell/d)+D.t*(Cycle61.Arithmetic.ell/d))) := (hselection j).2.2
  choose selected hselectedMain hcapacity hselected using hchoices
  let Pmain (i:rows') := ∏s∈main,Q i.val s
  let Pnorm (i:rows') := Pmain i / (((U^(D.t*(Cycle61.Arithmetic.ell/d)):ℝ)):ℂ)
  have hfull (i:rows') : ‖Pnorm i‖ ≤ U^(q*(Cycle61.Arithmetic.ell/d)) := by
    apply upper_bin_normalized (Pmain i) U (q*(Cycle61.Arithmetic.ell/d)) (D.t*(Cycle61.Arithmetic.ell/d)) hU0
    rw [hUZ]
    exact (hselected 0 i.val i.property).2 (hupper i.val i.property)
  have hcap (j:ℕ) (_:j∈Finset.range (coefficientBoxCount100 D.t+1)) :
      (∑s∈selected j,D.length s/d)  ≤  capOld D.momentKappa d ((j:ℝ)*D.t+D.t+D.t) := by
    exact hcapacity j
  have hlow (j:ℕ) (_:j∈Finset.range (coefficientBoxCount100 D.t+1)) (i:rows') :
      U^(q*capOld D.momentKappa d ((j:ℝ)*D.t+D.t+D.t)-
        ((2*a-1)*Cycle25.sourceMesh D.t/2))  ≤  ‖∏s∈selected j,Q i.val s‖ := by
    rw [hUZ]
    exact squared_selected_lower (Z^d) q _ (2*a-1) (Cycle25.sourceMesh D.t) _
      (by rw [←hUZ];exact hU0) (hselected j i.val i.property).1
  have hcrude (j:ℕ) (_:j∈Finset.range (coefficientBoxCount100 D.t+1)) (i:rows') :
      ‖∏s∈selected j,Q i.val s‖ ≤ U := by
    rw [hUZ]
    exact old_source_selected_product_crude D Z d ((j:ℝ)*D.t+D.t+D.t) (2*a-1) hZ ⟨hd,hdmax⟩ (by positivity) hδ hδtop (selected j) (Q i.val)
      (hcapacity j) (hupper i.val i.property)
  have hb := hbin.2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim
    rows' (fun u hu=>hrows u (hsub hu)) (fun u hu=>hrow u (hsub hu)) hdis hη Pbase selected Pnorm
    q R ((2*a-1)*Cycle25.sourceMesh D.t/2) Ccount hq0 hqtop hCc hcard hfull hcap hlow hcrude
  have hrestore := restore_upper_bin_loss Finset.univ
    (fun i:rows'=>labelPolynomialPacket F.S F.exclusions η i.val
      (fun s:J=>sourcePrimePool F Z s.val) (fun s=>source_prime_pool_outside F Z s.val)
      (fun _=>F.W) (fun s=>Z^(D.length s.val)) x z F.W (U^(y/d))) Pmain U (D.t*(Cycle61.Arithmetic.ell/d))
    (D.t+q*(Cycle61.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
      (3*R+1+D.t+D.t)/4+((2*a-1)*Cycle25.sourceMesh D.t/2)/2+(2*a-1)*(D.t+D.t)/2)
    (C*Ccount*(1+height)^degree*(U^(y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ))))
    hU0 hb
  have he : ((2*a-1)*Cycle25.sourceMesh D.t/2)/2=(2*a-1)*Cycle25.sourceMesh D.t/4 := by ring
  simpa only [he,Pmain] using hrestore



end Cycle61.Numerator.Source

end
/- END ORIGINAL Cycle61.Numerator.Source.OldClass -/

/- BEGIN ORIGINAL Cycle61.Numerator.Source.OldCollect; sha256 ec882ed2eec0d5fd3ee76eb6cf4761e67f79d689f01ee5f5e71210402cb65054 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                        
                                     
                                      
                                        
                                     

noncomputable section
set_option maxHeartbeats 2800000
open scoped Classical BigOperators ContDiff
open Filter
namespace Cycle61.Numerator.Source
open Cycle61.Arithmetic Cycle61.Arithmetic.Bernstein Cycle61.Numerator.OldFourth
open Cycle61.Numerator.Scalar
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle61DetectorCount Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

/-- A literal physical error-mask sum has the uniform pre-height certificate
exponent, with only the original full-class count and actual scalar as inputs. -/
theorem old_source_mask_amplitude_class (D:BaselineData)
    (hgap:theta < HeckeZeroSupremum.beta)
    (hbetatop : HeckeZeroSupremum.beta ≤ 7/8)
    (hkap : D.momentKappa=2*HeckeZeroSupremum.beta-1)
    (F:BaselineSourceData D) (hbeta:(51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (eps sigma : ℝ) (heps : 0<eps) (hsigma : 0 ≤ sigma)
    (hbudget : 16*D.e+2*eps+3*sigma/4+8*D.t ≤ (HeckeZeroSupremum.beta-theta)/4)
    (hfine:∀j,D.length j ≤  Cycle25.sourceMesh D.t/200) (J:Finset (Fin D.N)) :
    ∃degree:ℕ,∃C:ℝ,0 < C ∧ ∀ᶠU:ℝ in atTop,
      1 < U ∧ ∀(Z d:ℝ),1 < Z  →  d0 ≤ d  →  d ≤ dMinus  →  U=Z^d  → 
      ∀(η:Character) (x z:ℂ) (a height:ℝ),(51/100:ℝ) ≤ a  →  a ≤ 7/8  → 
      x.re=a+16*D.e  →  z.re=17/50  →  0 ≤ height  →  |z.im| ≤ height  → 
      ∀rows:Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U)  → 
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)  → 
      (∀P:∀i:J,sourcePrimePool F Z i.val,Function.Injective (fun i=>(P i).val))  → 
      (∀i P,P∈sourcePrimePool F Z i → IsCoprime P.val η.modulus)  → 
      (∀i P,P∈sourcePrimePool F Z i → (4:ℝ) ≤ P.val.absNorm)  → 
      (∀i,∀P∈F.S,(P.absNorm:ℝ) ≤ Z^(D.length i))  → 
      (∀i:J,sourcePrimePool F Z i.val)  → 
      ∀bin:BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
      let main := (Finset.univ:Finset (Fin D.N)) \ J
      let q := weightedMean Finset.univ (fun s=>D.length s/d)
        (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty  →  ∀Cs K C0:ℝ,0 ≤ Cs  →  1 ≤ K  →  1 ≤ C0  → 
      (rows'.card:ℝ) ≤ K*C0*Z^(3*D.t)*U^(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)  → 
      (∀u∈rows',‖frequencyWeight z ⟨u.val,u.property.1⟩*numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖ ≤ 
        Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*U^(2*eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t))  → 
      (∀u∈rows',∀s,‖Q u s‖ ≤ (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
      ‖sourceMaskContribution F η rows' J Z x z (Z^Cycle61.Arithmetic.y)‖  ≤ 
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^((degree:ℝ)+2*eps)*
          Z^(Assembly.signal HeckeZeroSupremum.beta-4999/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
  obtain ⟨degree,C,hC,hclass⟩ := old_source_packet_amplitude_class D F hbeta (by rw [hkap]) hfine J
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [hclass] with U hclass
  refine ⟨hclass.1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow hdis hη hQ hS Pbase bin
  dsimp only
  let Q := fun (u:FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
  let main := (Finset.univ:Finset (Fin D.N)) \ J
  let q := weightedMean Finset.univ (fun s=>D.length s/d)
    (maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
  intro hne Cs K C0 hCs hK hC0 hcard hscalar hupper
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hU0 : 0 < U := zero_lt_one.trans hclass.1
  have hd0 : 0 < d := d0_pos.trans_le hd
  have hδ : 0 < 2*a-1 := by linarith
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have hY : U^(Cycle61.Arithmetic.y/d)=Z^Cycle61.Arithmetic.y := by
    rw [hUZ,←Real.rpow_mul hZ0.le,mul_div_cancel₀ _ hd0.ne']
  have hcount1 : 1 ≤ K*C0*Z^(3*D.t) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hK hC0)
      (Real.one_le_rpow hZ.le (by have := D.t_pos;positivity))
  have hb := hclass.2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hheight hzim rows hrows hrow
    hdis hη Pbase bin hne (countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)
    (K*C0*Z^(3*D.t)) hcount1 hcard hupper
  have heq (u:FreeRow) (hu:u∈rows') := errorLabelNumerator_eq_packet F.S F.exclusions (4*D.e) F.first η u
    (hrow u (hsub hu)) J (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) hdis hη hQ
    (fun _=>F.W) (fun s=>Z^(D.length s)) x z (by rw [hx];linarith [D.e_pos]) hz.ge
    (by rw [hx];linarith [D.e_pos]) F.W 1 2 (by norm_num) F.complex_support (F.W.smooth ⊤)
    (Z^Cycle61.Arithmetic.y) (Real.rpow_pos_of_pos hZ0 _)
  have hlabel : (∑u∈rows',‖errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) x z F.W (Z^Cycle61.Arithmetic.y)*
      (∏s∈main,Q u s)‖)  ≤ 
    C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(Cycle61.Arithmetic.y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(Cycle61.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
        (3*(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+D.t+D.t)/4+
        (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Cycle61.Arithmetic.ell/d)) := by
    convert hb using 1
    calc
      _ = ∑i:rows',‖errorLabelNumerator F.S F.exclusions η i.val J (sourcePrimePool F Z)
          (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) x z F.W (Z^Cycle61.Arithmetic.y)*
          (∏s∈main,Q i.val s)‖ := (Finset.sum_coe_sort rows' _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [heq i.val i.property,hY]
  let A := Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*U^(2*eps)*
    U^(-(17/50:ℝ))*Z^((17/25)*D.t)
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have hphysical := source_mask_physical_front F η rows' J Z hZ0 x z hz (Z^Cycle61.Arithmetic.y) hS A _ hA hscalar hlabel
  have hselection := old_source_class_main_selection D F hfine Z d 0 (2*a-1) hZ ⟨hd,hdmax⟩ (by norm_num) hδ.le z rows main bin hne
  have hq0 : 0 ≤ q := hselection.1
  have hqmax : q ≤ (2*a-1)/2 := hselection.2.1
  have he := Scalar.source_packet_multiplicative_identity J D.length D.slots_sum Z D.momentKappa d
    (oldCapacityAt D.momentKappa d) (2*a-1) q (C*K*C0*((1+height)^degree)) (physicalLoss D eps sigma 0)
    hZ0 hd0.ne' hδ.ne'
  have hcapscale : oldCapacityAt D.momentKappa d/d=baseCapacity D.momentKappa d := by
    apply (div_eq_iff hd0.ne').mpr
    simpa only [mul_comm] using (base_scaled (κ:=D.momentKappa) hd0).symm
  rw [hcapscale] at he
  dsimp [physicalLoss] at he
  have hcollapse : A*Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i ∉ J},D.length j.val))*
      (C*(K*C0*Z^(3*D.t))*(1+height)^degree*(U^(Cycle61.Arithmetic.y/d))^(-(1/2:ℝ))*(∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
      U^(D.t+q*(Cycle61.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
        (3*(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+D.t+D.t)/4+
        (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Cycle61.Arithmetic.ell/d))) =
      (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*(1+height)^degree*
        Z^(numeratorExponent D.momentKappa d (oldCapacityAt D.momentKappa d) (2*a-1) (q/(2*a-1))+
          weightedSourceLoss d (2*a-1) (physicalLoss D eps sigma 0)) := by
    dsimp only [A]
    rw [hUZ]
    calc
      _ = (Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps))*
          (((Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*D.t)*
            Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i ∉ J},D.length j.val)))*
          (C*(K*C0*Z^(3*D.t))*(1+height)^degree*((Z^d)^(Cycle61.Arithmetic.y/d))^(-(1/2:ℝ))*
            (∏s:J,(Z^(D.length s.val))^(-(4/25:ℝ)))*
            (Z^d)^(D.t+q*(Cycle61.Arithmetic.ell/d)-q*baseCapacity D.momentKappa d/2+
              (3*(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma)+1+D.t+D.t)/4+
              (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2+D.t*(Cycle61.Arithmetic.ell/d)))) := by ring
      _ = _ := by
        have hex : (2*a-1)*(Cycle25.sourceMesh D.t+4*D.t)/4 =
          (2*a-1)*Cycle25.sourceMesh D.t/4+(2*a-1)*(D.t+D.t)/2 := by ring
        rw [hex] at he
        have hat : (Finset.univ : Finset J)=J.attach := rfl
        rw [←hat] at he
        dsimp only [physicalLoss]
        simp only [add_zero,zero_div,add_assoc] at he
        convert congrArg
          (fun r : ℝ => (Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps))*r) he using 1 <;> ring
  have hphysical' := hphysical.trans_eq hcollapse
  have hheightpow : (1+height)^degree  ≤  (3+height)^(degree:ℝ) := by
    rw [Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hcert := old_physical_packet_certificate D eps sigma d a q hgap hbetatop hkap heps.le hsigma hbudget ⟨hd,hdmax⟩ ha hatop ⟨hq0,hqmax⟩
  apply hphysical'.trans
  calc
    _  ≤  (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*(3+height)^(degree:ℝ)*
        Z^(Assembly.signal HeckeZeroSupremum.beta-4999/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hheightpow (by positivity)
      · exact Real.rpow_le_rpow_of_exponent_le hZ.le hcert
      · positivity
      · positivity
    _ = _ := by rw [Real.rpow_add (by linarith : 0 < 3+height) (degree:ℝ) (2*eps)];ring


theorem old_source_integrated_amplitude_classes (D : BaselineData)
    (hgap : theta < HeckeZeroSupremum.beta)
    (hbetatop : HeckeZeroSupremum.beta ≤ 7/8)
    (hkap : D.momentKappa=2*HeckeZeroSupremum.beta-1)
    (F : BaselineSourceData D) (hbeta : (51/100:ℝ)  ≤  HeckeZeroSupremum.beta)
    (eps sigma : ℝ) (heps : 0<eps) (hsigma : 0 ≤ sigma)
    (hbudget : 16*D.e+2*eps+3*sigma/4+8*D.t ≤ (HeckeZeroSupremum.beta-theta)/4)
    (hfine : ∀j,D.length j  ≤  Cycle25.sourceMesh D.t/200) :
    ∃Jw : ℝ,0  ≤  Jw ∧ ∃C : ℝ,0 < C ∧ ∀ᶠU : ℝ in atTop,
      1 < U ∧ ∀(Z d : ℝ),1 < Z  →  d0  ≤  d  →  d  ≤  dMinus  →  U=Z^d  → 
      ∀(η : Character) (x z : ℂ) (a height : ℝ),(51/100:ℝ)  ≤  a  →  a  ≤  7/8  → 
      x.re=a+16*D.e  →  z.re=17/50  →  0  ≤  height  →  |z.im|  ≤  height  → 
      ∀rows : Finset FreeRow,
      (∀u∈rows,U^(1/100:ℝ)  ≤  rowNorm u ∧ rowNorm u  ≤  U)  → 
      (∀u∈rows,(rowCharacter F.S F.exclusions.prime u).residue≠1)  → 
      (∀J : Finset (Fin D.N),∀P : ∀i:J,sourcePrimePool F Z i.val,
        Function.Injective (fun i=>(P i).val))  → 
      (∀P : ∀i,sourcePrimePool F Z i,Function.Injective (fun i=>(P i).val))  → 
      (∀i P,P∈sourcePrimePool F Z i  →  IsCoprime P.val η.modulus)  → 
      (∀i P,P∈sourcePrimePool F Z i  →  (4:ℝ)  ≤  P.val.absNorm)  → 
      (∀i,∀P∈F.S,(P.absNorm:ℝ)  ≤  Z^(D.length i))  → 
      (∀i,sourcePrimePool F Z i)  → 
      ∀Cs K C0 : ℝ,0  ≤  Cs  →  1  ≤  K  →  1  ≤  C0  → 
      let Q := fun (u : FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude
        F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
      (∀J : Finset (Fin D.N),∀bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t,
        let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
        let q := weightedMean Finset.univ (fun s=>D.length s/d)
          (maskedGain (Finset.univ\J) (binValue Finset.univ ((2*a-1)/2) D.t bin))
        rows'.Nonempty  →  (rows'.card:ℝ)  ≤  K*C0*Z^(3*D.t)*
          U^(countingR D.momentKappa (2*a-1) (q/(2*a-1))+sigma))  → 
      (∀u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩*
        numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖  ≤ 
        Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^(2*eps)*
          U^(2*eps)*U^(-(17/50:ℝ))*Z^((17/25)*D.t))  → 
      (∀u∈rows,∀s,‖Q u s‖  ≤  (Z^(D.length s))^
        (HeckePrimeAmplitudeBins.amplitude (Z^(D.length s)) ((2*a-1)/2) D.t (Q u s)+D.t))  → 
      ‖Cycle25.Weighted.FullWContour.integratedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
        (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) F.W (Z^Cycle61.Arithmetic.y) x z‖  ≤ 
        (C*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*(3+height)^Jw*
          Z^(Assembly.signal HeckeZeroSupremum.beta-4999/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := by
  choose degree Cmask hCmask hmask using (fun J : Finset (Fin D.N)=>old_source_mask_amplitude_class D hgap hbetatop hkap F hbeta eps sigma heps hsigma hbudget hfine J)
  obtain ⟨Jw,hJw,Ctot,hCtot,hcoeff,hheight⟩ := finite_height_envelope degree Cmask hCmask
  let classFactor : ℝ := (HeckeDetectorClassBudget.alphabetBound D.t:ℝ)^D.N
  let maskFactor : ℝ := (2:ℝ)^D.N
  have hcf : 0 < classFactor := by
    unfold classFactor HeckeDetectorClassBudget.alphabetBound
    positivity
  have hmf : 0 < maskFactor := by dsimp only [maskFactor];positivity
  refine ⟨Jw+2*eps,by linarith [heps],(2*Real.pi)*classFactor*maskFactor*Ctot,
    by positivity,?_⟩
  filter_upwards [Filter.eventually_all.mpr hmask] with U hall
  refine ⟨(hall ∅).1,?_⟩
  intro Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hH him rows hrows hrow
    hdis hdisAll hη hQ hS Pbase Cs K C0 hCs hK hC0
  dsimp only
  let Q := fun (u : FreeRow) s=>HeckePrimeRow.canonicalPrimeAmplitude
    F.modulus ⊤ u.val F.W 2 (Z^(D.length s)) z
  let classRows := fun bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t=>
    amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun s=>D.length s/d) Q bin
  intro hcount hscalar hupper
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  let common : ℝ := Cs*K*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(Assembly.signal HeckeZeroSupremum.beta-4999/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e)
  let A : ℝ := common*Ctot*(3+height)^(Jw+2*eps)
  have hcommon : 0  ≤  common := by dsimp only [common];positivity
  have hA : 0  ≤  A := by dsimp only [A];positivity
  have hmaskBound (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
      (hne : (classRows bin).Nonempty) (J : Finset (Fin D.N)) :
      ‖sourceMaskContribution F η (classRows bin) J Z x z (Z^Cycle61.Arithmetic.y)‖  ≤  A := by
    have hsub : classRows bin  ⊆  rows := Finset.filter_subset _ _
    have hh := (hall J).2 Z d hZ hd hdmax hUZ η x z a height ha hatop hx hz hH him
      rows hrows hrow (hdis J) hη hQ hS (fun j:J=>Pbase j.val) bin hne Cs K C0 hCs hK hC0
      (hcount J bin hne) (fun u hu=>hscalar u (hsub hu)) (fun u hu=>hupper u (hsub hu))
    have he := (hheight height eps hH heps.le).1 J
    calc
      _  ≤  (Cmask J*Cs*K)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          (3+height)^((degree J:ℝ)+2*eps)*
          Z^(Assembly.signal HeckeZeroSupremum.beta-4999/5000000000-(HeckeZeroSupremum.beta-theta)/2-D.t-kernelExponent a D.e) := hh
      _ = common*(Cmask J*(3+height)^((degree J:ℝ)+2*eps)) := by dsimp only [common];ring
      _  ≤  common*(Ctot*(3+height)^(Jw+2*eps)) := mul_le_mul_of_nonneg_left he hcommon
      _ = A := by dsimp only [A];ring
  have hclass (bin : BinLabel (Finset.univ:Finset (Fin D.N)) ((2*a-1)/2) D.t)
      (hne : (classRows bin).Nonempty) :
      ‖reconstructedDyadValue F.S F.exclusions F.maximal η (classRows bin) (sourcePrimePool F Z)
        (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s)) x z F.W (Z^Cycle61.Arithmetic.y)‖  ≤  maskFactor*A := by
    calc
      _ = ‖∑J∈Finset.univ.powerset,sourceMaskContribution F η (classRows bin) J Z x z (Z^Cycle61.Arithmetic.y)‖ :=
        congrArg norm (source_reconstructed_sum_masks F η (classRows bin) Z x z (Z^Cycle61.Arithmetic.y))
      _  ≤  ∑J∈Finset.univ.powerset,A := by
        apply (norm_sum_le _ _).trans
        exact Finset.sum_le_sum (fun J _=>hmaskBound bin hne J)
      _ = maskFactor*A := by
        simp only [Finset.sum_const,Finset.card_powerset,Finset.card_univ,Fintype.card_fin,
          nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
        rfl
  have hr := reconstructedDyadValue_class_uniform F.S F.exclusions F.maximal η rows
    (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) (fun _=>F.W) (fun s=>Z^(D.length s))
    x z F.W (Z^Cycle61.Arithmetic.y) Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (by linarith)
    (fun s=>D.length s/d) Q (maskFactor*A) (mul_nonneg hmf.le hA) hclass
  have heq := integratedDyadValue_reconstruction F.S F.exclusions F.maximal (4*D.e) F.first η rows hrow
    (sourcePrimePool F Z) (fun s=>source_prime_pool_outside F Z s) hdis hdisAll hη hQ
    (fun _=>F.W) (fun s=>Z^(D.length s)) x z (by rw [hx];linarith [D.e_pos]) hz.ge
    (by rw [hx];linarith [D.e_pos]) F.W 1 2 (by norm_num) F.complex_support (Z^Cycle61.Arithmetic.y)
    (Real.rpow_pos_of_pos hZ0 _)
  rw [heq,norm_mul]
  have hpi : ‖(2*Real.pi:ℂ)‖=2*Real.pi := by
    rw [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hpi]
  apply (mul_le_mul_of_nonneg_left hr (by positivity : 0  ≤  2*Real.pi)).trans_eq
  simp only [Finset.card_univ,Fintype.card_fin]
  dsimp only [classFactor,maskFactor,A,common]
  ring



end Cycle61.Numerator.Source

end
/- END ORIGINAL Cycle61.Numerator.Source.OldCollect -/
