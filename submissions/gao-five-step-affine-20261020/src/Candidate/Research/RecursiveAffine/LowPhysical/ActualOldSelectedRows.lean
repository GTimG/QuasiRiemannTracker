/- Copyright (c) 2026 Hailey Collet; actual recursive OLD source assembly (c) 2026 Zhongpai Gao.
Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.LowPhysical.NativeOldAllowance
import Candidate.Research.RecursiveAffine.LowPhysical.ActualFirstMass
import Candidate.Research.RecursiveAffine.LowPhysical.NativeFirstShells
import Candidate.Research.RecursiveAffine.NativeSelectedForest
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle153LowPhysical
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass Cycle153RegionalLow
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstAmplificationChoice CenteredMomentFirstDiscardedEnergy
open Cycle63FinalCapacity CenteredMomentSectorLocalization
open CenteredMomentSourceLiveColumn CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentCommonAllocationSum CenteredMomentLogDyadic CenteredMomentWholeDivisorShell
open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplifiedRetainedRadius
open CenteredMomentCanonicalFirst CenteredMomentFirstExceptionalPrefactor

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {Label : Type} [Fintype Label]

/-- Literal OLD row term of the actual native selected LOW source. -/
def nativeOldSelectedCost
    (reflected second : Bool) (s : Input alpha) (R : Ideal O)
    (Z Mrow amp xi reserve b firstHeight : ℝ) (Nrow : ℕ) (hZ : 1< Z)
    (key : ℤ×(Fin 5→ℤ)) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s R 1 (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (Psi : 𝓢(ℝ,ℂ)) (epsMass epsShell error Cg fixed : ℝ) : ℝ :=
  let first:=fun l=>geometryFirstLabel s R 1 (Z^Mrow) Z xi
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val
  let Rows:=NativeLowRows reflected s R 1 Z Mrow amp xi reserve b firstHeight Nrow hZ key hz1 hz2 firstIndex
  let childSrc:=fun l=>geometryLowFirstChild reflected s R 1 (Z^Mrow) Z xi
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight (firstIndex l)
  let lab:=fun r : Rows=>actualSecondSupportedLabel _ _ _ _ _ _ _ r.val.2
    (actual_main_low_selected_inactive reflected s R 1 Z Mrow amp xi reserve b firstHeight Nrow
      hZ key hz1 hz2 firstIndex r)
  let mass:=fun l=>geometryFirstHighMass reflected s R 1 Psi Mrow Z xi epsMass
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val
  let pay0:=fun r : Rows=>Z^(-amp)*
    (firstMainRadius reflected (Z^Mrow) (volume s) Z xi (3*amp) reserve (first r.val.1)/volume (childSrc r.val.1))*
    (normalizer (lab r).1.1 (lab r).1.2 (lab r).2.val*
      ((if second then (lab r).1.2 else (lab r).1.1).absNorm:ℝ)^(epsShell-1))*
    Z^(secondNominal 1 Z amp (frequencyLoss Z 32 xi+reserve)
      (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
      (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
      (lab r).1.1 (lab r).1.2 (lab r).2.val+amp+error)
  let allowance:=fun r : Rows=>lowAllowance Z
    (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
    (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
    (lab r).1.1 (lab r).1.2 (if second then (lab r).1.2 else (lab r).1.1)
  ∑r : Rows,Cg*fixed*(mass r.val.1*Z^amp)*(pay0 r*Z^(allowance r))

/-- The genuine native allowance source bound, specialized to the SAME
actual selected rows used by the recursive LOW forest. Actual first mass
and side come from one original geometry bin. Only OLD is split by its
first-projector shell; the returned forest is absent from this operator. -/
theorem eventual_actual_selected_old_rows
    (N : ℕ) (supply ap epsV Bnorm epsLabels U epsFirst : ℝ)
    (hsupply : 0< supply) (hap : 0< ap) (hV : 0< epsV) (hB : 0≤ Bnorm)
    (hLabels : 0< epsLabels) (hU : 0≤ U) (hFirst : 0< epsFirst) :
    ∃Kold : ℝ,0< Kold ∧ ∀ᶠ Z : ℝ in atTop,2≤ Z ∧
    ∀{alpha Label : Type}[Fintype alpha][DecidableEq alpha][Fintype Label]
      (reflected second : Bool)(s : Input alpha)(R : Ideal O)
      (Mrow amp xi reserve b firstHeight Bmass epsMass epsShell error Cg fixed : ℝ)
      (Nrow : ℕ)(hZ : 1< Z)(key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
      (firstIndex : Label→GeometryLowFirstIndex reflected s R 1 (Z^Mrow) Z xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)(Psi : 𝓢(ℝ,ℂ)),
    Fintype.card alpha≤ N → supply≤ s.lower →
    (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤ Z^U) →
    sourceRadius s≤ Z^Bmass → Bmass+1≤ Bnorm → 0≤ epsMass → 0≤ epsShell → 0≤ Cg → 0≤ fixed →
    (∀x,s.W₁ x≠0→ap≤ x) → (∀x,s.W₂ x≠0→ap≤ x) →
    (∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s R 1 (Z^Mrow) Z xi
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val) R s.ν s.W s.P≠0) →
    Function.Injective (fun l=>(geometryFirstLabel s R 1 (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val,(firstIndex l).1.val.2.1.val)) →
    (∀l,sourceRadius (geometryLowFirstChild reflected s R 1 (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight (firstIndex l))≤ Z^Bnorm) →
    ∀box : Finset (Fin 4→ℤ),
    (∀r : NativeLowRows reflected s R 1 Z Mrow amp xi reserve b firstHeight Nrow hZ key hz1 hz2 firstIndex,
      actualSecondDyad
        (geometryLowFirstChild reflected s R 1 (Z^Mrow) Z xi
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight (firstIndex r.val.1))
        (R*geometryColumnIdeal reflected s R 1 (Z^Mrow) Z xi
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex r.val.1).1.val)
        (firstIndex r.val.1).1.val.2.1.val
        (firstMainRadius reflected (Z^Mrow) (volume s) Z xi (3*amp) reserve
          (geometryFirstLabel s R 1 (Z^Mrow) Z xi (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
            key (firstIndex r.val.1).1.val))
        (firstMainFourierScale reflected (Z^Mrow) (volume s) Z xi (3*amp) reserve b
          Nrow (geometryFirstLabel s R 1 (Z^Mrow) Z xi
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex r.val.1).1.val)) Z xi r.val.2∈box) →
    nativeOldSelectedCost reflected second s R Z Mrow amp xi reserve b firstHeight Nrow hZ key hz1 hz2
      firstIndex Psi epsMass epsShell error Cg fixed≤
      Kold*Cg*fixed*geometryHighFactor reflected (geometrySupportConstant N supply ap ap) key*(box.card:ℝ)*
        Z^(Bmass*epsMass+amp+error+(1-Mrow)+epsV+Bnorm*epsShell+epsLabels+epsFirst) := by
  obtain ⟨K0,hK0,hpaid⟩:=eventual_actual_old_mass_allowance N supply epsV Bnorm epsLabels hsupply hV hB hLabels
  obtain ⟨Cfirst,hCfirst,hcount⟩:=eventual_actual_old_first_shell_sum N U epsFirst hU hFirst
  refine ⟨64*Cfirst*K0,by positivity,?_⟩
  filter_upwards [hpaid,hcount] with Z hp hc
  refine ⟨hp.1,?_⟩
  intro alpha Label _ _ _ reflected second s R Mrow amp xi reserve b firstHeight Bmass epsMass epsShell
    error Cg fixed Nrow hZ key hz1 hz2 firstIndex Psi hN hlower hpool hsource hBstrong hMass hShell hCg hfixed
    hs1 hs2 hf hinj hchildsource box hbox
  let hK:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
  let first:=fun l=>geometryFirstLabel s R 1 (Z^Mrow) Z xi hK key (firstIndex l).1.val
  let childSrc:=fun l=>geometryLowFirstChild reflected s R 1 (Z^Mrow) Z xi hK key firstHeight (firstIndex l)
  let Rchild:=fun l=>R*geometryColumnIdeal reflected s R 1 (Z^Mrow) Z xi hK key (firstIndex l).1.val
  let seed:=fun l=>(firstIndex l).1.val.2.1.val
  let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z xi (3*amp) reserve (first l)
  let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z xi (3*amp) reserve b Nrow (first l)
  let rows:=mainLowSelectedNonzeroRows reflected s R 1 Z Mrow amp xi reserve b firstHeight Nrow hZ key hz1 hz2 firstIndex
  let mass:=fun l=>geometryFirstHighMass reflected s R 1 Psi Mrow Z xi epsMass hK key (firstIndex l).1.val
  let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) key
  have hphysical : 0≤ physical:=(geometry_high_factor_pos reflected
    (geometrySupportConstant N supply ap ap) key (geometrySupportConstant_pos N supply ap ap hsupply hap hap)).le
  obtain ⟨exponent,sideLower,hledger,hgate⟩:=actual_first_mass_and_old_side reflected N supply ap hsupply hap
    s R 1 Psi Mrow Z xi Bmass epsMass hZ hN hlower (by simp) hz1 hz2 hsource hMass hs1 hs2 key
  have hfirst:=actual_main_low_first_source_gates reflected s R 1 (Z^Mrow) Z xi Bmass hK
    (by simp) hz1 hz2 hsource key firstIndex
  let p:=((key.2 2:ℝ)+1)*Real.logb Z 2
  let cost : rows→ℝ:=fun r=>
    let lab:=actualSecondSupportedLabel (childSrc r.val.1) (Rchild r.val.1) (seed r.val.1)
      (K r.val.1) (Tsec r.val.1) Z xi r.val.2
      (actual_main_low_selected_inactive reflected s R 1 Z Mrow amp xi reserve b firstHeight Nrow hZ key hz1 hz2 firstIndex r)
    Cg*fixed*(mass r.val.1*Z^amp)*
      ((Z^(-amp)*(K r.val.1/volume (childSrc r.val.1))*
        (normalizer lab.1.1 lab.1.2 lab.2.val*((if second then lab.1.2 else lab.1.1).absNorm:ℝ)^(epsShell-1))*
        Z^(secondNominal 1 Z amp (frequencyLoss Z 32 xi+reserve)
          (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
          (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2) lab.1.1 lab.1.2 lab.2.val+amp+error))*
      Z^(lowAllowance Z (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
        (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2) lab.1.1 lab.1.2
        (if second then lab.1.2 else lab.1.1)))
  let oldBound:=64*Cg*fixed*physical*(box.card:ℝ)*K0*
    Z^(Bmass*epsMass+amp+error+(1-Mrow)+epsV+Bnorm*epsShell+epsLabels)
  have hold : 0≤oldBound :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (by norm_num : (0:ℝ)≤64) hCg) hfixed) hphysical) (Nat.cast_nonneg _)) hK0.le)
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hshell : ∀n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val)),
      (∑q : mainLowShellRows reflected s R 1 Z Mrow amp xi reserve b firstHeight Nrow hZ key firstIndex rows n,
        cost (mainLowShellRowOriginal reflected s R 1 Z Mrow amp xi reserve b firstHeight Nrow hZ key firstIndex rows n q))≤ oldBound := by
    intro n hn
    let fi:=fun l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n=>firstIndex l.val
    let rs:=mainLowShellRows reflected s R 1 Z Mrow amp xi reserve b firstHeight Nrow hZ key firstIndex rows n
    let old:=mainLowShellRowOriginal reflected s R 1 Z Mrow amp xi reserve b firstHeight Nrow hZ key firstIndex rows n
    have hg:=actual_main_low_final_shell_first_gates reflected s R 1 Z Mrow xi hZ key hz1 hz2 firstIndex
      Bmass Bnorm hp.1 (by simp) hsource hBstrong hinj hf n hn
    have hT:=(actual_geometry_selected_first_shell_scale s N R 1 (Z^Mrow) Z xi U hK hN hZ.le hU hpool key
      (fun l=>(firstIndex l).1.val) n hn).1
    have hnw : Bmass≤ Bnorm:=by linarith only [hBstrong]
    have hnorm (l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n) := hfirst l.val
    have hk:=hp.2 s hN hlower reflected second (fun l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n=>first l.val)
      (fun l=>⟨(hnorm l).1,(hnorm l).2.1⟩) (fun l=>(hnorm l).2.2.1) R (fun l=>(fi l).2)
      (fun l=>geometryColumnCharacter reflected s R 1 (Z^Mrow) Z xi hK key (fi l).1.val)
      (fun _=>firstHeight) (fun l=>hf l.val)
      (fun l=>Rchild l.val) (fun l=>seed l.val) (fun l=>K l.val) (fun l=>Tsec l.val)
      xi 1 Mrow amp reserve error epsShell
      (fun l=>(hnorm l).2.2.2.2.2.2.2) (fun _=>hz1) (fun _=>hz2) hShell (fun l=>hchildsource l.val)
      (dyadicScale n) p exponent hT hg.2.2.2 1 (by simp) one_ne_zero hg.1
      (fun _=>⟨one_dvd _,one_dvd _⟩)
      (fun l=>⟨(hnorm l).2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hnw),
        (hnorm l).2.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hnw)⟩)
      (fun l=>(actual_geometry_low_bin_gate_side s R 1 (Z^Mrow) Z xi Bmass (Real.logb Z (volume s))
        hK hZ (by simp) hz1 hz2 hsource key reflected).choose_spec.choose_spec.2 (fi l).1.val |>.1)
      (fun l=>(hgate (fi l).1.val).1) hg.2.2.1
      rs (fun q hq=>actual_main_low_selected_inactive reflected s R 1 Z Mrow amp xi reserve b firstHeight Nrow hZ key
        hz1 hz2 firstIndex (old ⟨q,hq⟩)) box
      (fun q hq=>hbox (old ⟨q,hq⟩))
      (fun l=>mass l.val) Cg fixed physical (Bmass*epsMass-sideLower) hCg hfixed hphysical
      (fun l=>(hgate (fi l).1.val).2.1)
    have he : (Bmass*epsMass-sideLower)+amp+p+exponent+error+(1-Mrow)+epsV+Bnorm*epsShell+epsLabels=
        (Bmass*epsMass+amp+error+(1-Mrow)+epsV+Bnorm*epsShell+epsLabels)+6*Real.logb Z 2 := by
      dsimp only [p] at hledger ⊢
      linarith only [hledger]
    apply hk.trans_eq
    change Cg*fixed*physical*(box.card:ℝ)*K0*
      Z^((Bmass*epsMass-sideLower)+amp+p+exponent+error+(1-Mrow)+epsV+Bnorm*epsShell+epsLabels)/
        ((1:Ideal O).absNorm:ℝ)=oldBound
    have hpow : Z^((Bmass*epsMass-sideLower)+amp+p+exponent+error+(1-Mrow)+epsV+Bnorm*epsShell+epsLabels)=
        Z^(Bmass*epsMass+amp+error+(1-Mrow)+epsV+Bnorm*epsShell+epsLabels)*64 := by
      rw [he,Real.rpow_add (zero_lt_one.trans hZ),geometry_low_bin_slack_six_payment Z hZ]
    rw [hpow]
    simp only [map_one,Nat.cast_one,div_one]
    dsimp only [oldBound]
    ring
  have hb:=hc.2 s hN hpool reflected R 1 Mrow amp xi reserve b firstHeight Nrow hZ key firstIndex rows cost oldBound hold hshell
  change (∑r : rows,cost r)≤_
  apply hb.trans_eq
  have hpow : Z^(Bmass*epsMass+amp+error+(1-Mrow)+epsV+Bnorm*epsShell+epsLabels+epsFirst)=
      Z^epsFirst*Z^(Bmass*epsMass+amp+error+(1-Mrow)+epsV+Bnorm*epsShell+epsLabels) := by
    rw [show Bmass*epsMass+amp+error+(1-Mrow)+epsV+Bnorm*epsShell+epsLabels+epsFirst=
      epsFirst+(Bmass*epsMass+amp+error+(1-Mrow)+epsV+Bnorm*epsShell+epsLabels) by ring,
      Real.rpow_add (zero_lt_one.trans hZ)]
  rw [hpow]
  dsimp only [oldBound]
  ring

end
end OAI.SevenEighths.Cycle153LowPhysical
#print axioms OAI.SevenEighths.Cycle153LowPhysical.eventual_actual_selected_old_rows
