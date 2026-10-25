/- Copyright (c) 2026 Sil. Apache-2.0.
Literal original-column L1 mass and the discarded Fourier density.
The cutoff theorem is reused; only its actual coefficient mass and
support cap are discharged here, with original prefix savings intact.
-/
import Candidate.Feedback.FourthPower.MixedPrincipalWindow
import Candidate.Feedback.FourthPower.MixedOriginalNormCap
import Candidate.Feedback.FourthPower.MixedLocalizedDictionary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.MixedOriginalTail
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentSourceZeroEnergy
open CenteredMomentSourceRectangle (plainSupportPool)
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice CenteredMomentTwist
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentFirstLocalization
open CenteredMomentSupportedTailAggregate CenteredMomentSecondTail CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedHeightEnergy MixedLiteralAllocation MixedTupleRows MixedCompletedRows
open MixedCommonCoefficient MixedCommonRestriction MixedOriginalNormCap
open MixedPoissonLocalization MixedLocalizedDictionary
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def supControl (W : 𝓢(ℝ,ℂ)) : ℝ := sourceControl {(0,0)} W

theorem supControl_nonneg (W : 𝓢(ℝ,ℂ)) : 0≤supControl W := sourceControl_nonneg _ _

theorem norm_le_supControl (W : 𝓢(ℝ,ℂ)) (x : ℝ) : ‖W x‖≤supControl W := by
  unfold supControl sourceControl
  rw [Finset.sup_singleton]
  exact SchwartzMap.norm_le_seminorm ℝ W x

def profileCap (s : Source ι a b) : ℝ :=
  2*supControl s.W₁*supControl s.W₂*(∏i,s.M i)

def poolCap (s : Source ι a b) : ℝ :=
  (128*b)^2*(s.X₁+s.Y₁)*(s.X₂+s.Y₂)/pairNorm s.d*(∏i,256*s.P i)

def massCap (s : Source ι a b) : ℝ := profileCap s*poolCap s

theorem profileCap_nonneg (s : Source ι a b) : 0≤profileCap s := by
  have := supControl_nonneg s.W₁
  have := supControl_nonneg s.W₂
  have hM : 0≤∏i,s.M i := Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hM i))
  unfold profileCap
  positivity

theorem poolCap_nonneg (s : Source ι a b) : 0≤poolCap s := by
  have := (s.hL.trans_le s.hX₁).le
  have := (s.hL.trans_le s.hX₂).le
  have := (s.hL.trans_le s.hY₁).le
  have := (s.hL.trans_le s.hY₂).le
  have hP : 0≤∏i,256*s.P i :=
    Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hP i)))
  have := (pairNorm_pos s.hd.1 s.hd.2).le
  unfold poolCap
  positivity

/-- The union of ordinary supports is counted at the EXACT divided
lengths. This also works when either length is below one. -/
theorem residual_plain_card (d : Id) (hd : d≠0) (b X Y : ℝ)
    (hb : 0≤b) (hX : 0≤X) (hY : 0≤Y) :
    ((residualPool d hd (plainSupportPool b X Y)).card:ℝ)≤128*b*(X+Y)/(d.absNorm:ℝ) := by
  rw [residual_plain_pool,plainSupportPool]
  calc
    _ ≤ ((idealBall (b*(X/d.absNorm))).card:ℝ)+(idealBall (b*(Y/d.absNorm))).card := by
      exact_mod_cast Finset.card_union_le (idealBall (b*(X/d.absNorm))) (idealBall (b*(Y/d.absNorm)))
    _ ≤ 128*(b*(X/d.absNorm))+128*(b*(Y/d.absNorm)) :=
      add_le_add (idealBall_card _ (mul_nonneg hb (div_nonneg hX (Nat.cast_nonneg _))))
        (idealBall_card _ (mul_nonneg hb (div_nonneg hY (Nat.cast_nonneg _))))
    _ = _ := by ring

theorem source_pool_card (s : Source ι a b) (hb : 0≤b) :
    ((Fintype.piFinset (tuplePools s)).card:ℝ)≤poolCap s := by
  have hp (i : ι) : ((s.pool i).card:ℝ)≤256*s.P i := by
    have hsub : s.pool i⊆idealBall (2*s.P i) := by
      intro I hI
      exact (mem_idealBall _ _).mpr ⟨(s.hpn i I hI).1.1,(s.hpn i I hI).2⟩
    calc
      _ ≤ ((idealBall (2*s.P i)).card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ 128*(2*s.P i) := idealBall_card _ (mul_nonneg (by norm_num) (zero_le_one.trans (s.hP i)))
      _ = _ := by ring
  have hprod : (∏i,((s.pool i).card:ℝ))≤∏i,256*s.P i :=
    Finset.prod_le_prod₀ (fun (i : ι) _=>Nat.cast_nonneg (s.pool i).card) (fun i _=>hp i)
  have hleft := residual_plain_card s.d.1 s.hd.1 b s.X₁ s.Y₁ hb
    (s.hL.trans_le s.hX₁).le (s.hL.trans_le s.hY₁).le
  have hright := residual_plain_card s.d.2 s.hd.2 b s.X₂ s.Y₂ hb
    (s.hL.trans_le s.hX₂).le (s.hL.trans_le s.hY₂).le
  have hup : 0≤∏i,256*s.P i :=
    Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hP i)))
  have hlup : 0≤128*b*(s.X₁+s.Y₁)/(s.d.1.absNorm:ℝ) := by
    have := (s.hL.trans_le s.hX₁).le
    have := (s.hL.trans_le s.hY₁).le
    positivity
  have hh := mul_le_mul (mul_le_mul hprod hleft (Nat.cast_nonneg _) hup) hright
    (Nat.cast_nonneg _) (mul_nonneg hup hlup)
  calc
    _ = (∏i,((s.pool i).card:ℝ))*
        ((residualPool s.d.1 s.hd.1 (plainSupportPool b s.X₁ s.Y₁)).card:ℝ)*
        ((residualPool s.d.2 s.hd.2 (plainSupportPool b s.X₂ s.Y₂)).card:ℝ) := by
      simp only [Fintype.card_piFinset,Nat.cast_prod,tuplePools,sourcePools,pools,
        Fintype.prod_sum_type,Fin.prod_univ_two,Sum.elim_inl,Sum.elim_inr,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Nat.cast_mul]
      ring
    _ ≤ (∏i,256*s.P i)*(128*b*(s.X₁+s.Y₁)/(s.d.1.absNorm:ℝ))*
        (128*b*(s.X₂+s.Y₂)/(s.d.2.absNorm:ℝ)) := hh
    _ = _ := by unfold poolCap pairNorm;ring

/-- Both ordinary heights have exactly unit modulus. The only profile
control is the homogeneous (0,0) seminorm of the original Schwartz maps. -/
theorem original_coefficient_mass (s : Source ι a b) (ha : 0<a) (hb : 0≤b) (seed : Id) :
    (∑I∈sourceColumns s,‖sourceCoefficient s ha seed I‖)≤massCap s := by
  let V₁ := normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁
  let V₂ := normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂
  let weight := fun v : Tuple ι=>tupleWeight (punctureProduct s.S s.H) v*
    profileCoefficient s.R s.ν s.Wslot s.P V₁ V₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 seed v
  have hprofile (v : Tuple ι) : ‖weight v‖≤profileCap s := by
    have hp := profileCoefficient_norm_le s.R s.ν s.hν s.Wslot s.P s.M V₁ V₂
      (supControl s.W₁) (supControl s.W₂) (fun i=>zero_le_one.trans (s.hM i))
      (supControl_nonneg s.W₁) (supControl_nonneg s.W₂) s.hWnorm
      (fun x=>by simpa only [V₁,normPowerProfile_norm] using norm_le_supControl s.W₁ x)
      (fun x=>by simpa only [V₂,normPowerProfile_norm] using norm_le_supControl s.W₂ x)
      s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 seed v
    have hw : ‖tupleWeight (punctureProduct s.S s.H) v‖≤1 := by
      unfold tupleWeight
      split_ifs <;> norm_num
    rw [show weight v=tupleWeight (punctureProduct s.S s.H) v*
      profileCoefficient s.R s.ν s.Wslot s.P V₁ V₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 seed v from rfl,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hw).trans hp
  calc
    _ ≤ ∑v∈Fintype.piFinset (tuplePools s),‖weight v‖ :=
      finiteColumnCoefficient_mass (Fintype.piFinset (tuplePools s)) weight
    _ ≤ ∑v∈Fintype.piFinset (tuplePools s),profileCap s := Finset.sum_le_sum (fun v _=>hprofile v)
    _ = ((Fintype.piFinset (tuplePools s)).card:ℝ)*profileCap s := by
      rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ poolCap s*profileCap s :=
      mul_le_mul_of_nonneg_right (source_pool_card s hb) (profileCap_nonneg s)
    _ = _ := by unfold massCap;ring

/-- The previously proved weighted support theorem applies to the same
literal source, including its arbitrary seed and tupleWeight. -/
theorem original_coefficient_cap (s : Source ι a b) (ha : 0<a) (seed I : Id)
    (hI : sourceCoefficient s ha seed I≠0) :
    I≠0 ∧ (I.absNorm:ℝ)≤sourceNormCap s.P b s.T s.d := by
  let V₁ := normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁
  let V₂ := normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂
  have hs₁ : Function.support (V₁:ℝ→ℂ)⊆Set.Icc a b :=
    (normPowerProfile_support _ _ _ _ _ _ _).trans s.hs₁
  have hs₂ : Function.support (V₂:ℝ→ℂ)⊆Set.Icc a b :=
    (normPowerProfile_support _ _ _ _ _ _ _).trans s.hs₂
  have hz (i : ι) : s.Wslot i 0=0 := by
    by_contra hn
    have h := (s.hW i hn).1
    norm_num at h
  have hz₁ : V₁ 0=0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hs₁ hn).1
  have hz₂ : V₂ 0=0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hs₂ hn).1
  have h := weighted_profile_column_norm (Fintype.piFinset (tuplePools s))
    (tupleWeight (punctureProduct s.S s.H)) s.R seed s.ν s.Wslot s.P (fun _=>(2:ℝ))
    V₁ V₂ b b s.X₁ s.X₂ s.Y₁ s.Y₂ s.d s.hd
    (fun i=>zero_lt_one.trans_le (s.hP i)) (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)
    (s.hL.trans_le s.hY₁) (s.hL.trans_le s.hY₂) (s.hpX.trans s.hpY.symm) hz hz₁ hz₂
    (fun i x hx=>(s.hW i hx).2) (fun x hx=>(hs₁ hx).2) (fun x hx=>(hs₂ hx).2) I hI
  refine ⟨h.1,h.2.trans_eq ?_⟩
  unfold sourceNormCap
  rw [s.hpX,Finset.prod_mul_distrib]
  ring

/-- Actual discarded source: its L1 norm and support are now proved,
not premises. K4 and its outer 1/W are exactly those of the dictionary. -/
theorem original_discarded_bound (Adec : ℕ) :
    ∃(control : Finset (ℕ×ℕ))(C : ℝ),0<C ∧
      ∀(ι : Type u) [Fintype ι],∀a b : ℝ,∀s : Source ι a b,∀ha : 0<a,0≤b→
      ∀(seed : Id)(η : Character)(t K W X H Tsec Z Csec ξ : ℝ),
      0<K→0<W→0<X→1<Z→1≤Csec→
      sourceNormCap s.P b s.T s.d≤Real.exp H*X→
      X^2/(16*K*W^4)≤Tsec→
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4)→
      ‖localizedDensity Finset.univ (sourceGenerator (sourceColumns s))
        (sourceGenerator_supported (sourceColumns s))
        (fun I : supportedColumns (sourceColumns s)=>sourceCoefficient s ha seed I*heightCoeff η t I)
        K W (discardedWeight (frequencyRadius Tsec Z ξ))‖≤
      ((massCap s)^2*(16*K*W^4)*(Real.exp H*X)^2*
        (C*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec))/W := by
  obtain ⟨control,C,hC,htail⟩ := source_discarded_bound Adec
  refine ⟨control,C,hC,?_⟩
  intro ι instι a b s ha hb seed η t K W X H Tsec Z Csec ξ hK hW hX hZ hCs hcap hsec hthreshold
  have htail := htail η t (sourceColumns s) (sourceCoefficient s ha seed)
    K W X H Tsec Z Csec ξ hK hW hX hZ hCs
    (fun I _ hI=>(original_coefficient_cap s ha seed I hI).2.trans hcap) hsec hthreshold
  let F := (16*K*W^4)*(Real.exp H*X)^2*
    (C*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile)/
    ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^Adec)/W
  have hF : 0≤F := by
    have := (show 0≤control.sup (schwartzSeminormFamily ℝ ℝ ℂ) ballProfile from apply_nonneg _ _)
    have := zero_lt_one.trans hZ
    dsimp only [F]
    positivity
  have hmass := pow_le_pow_left₀
    (Finset.sum_nonneg (fun I _=>norm_nonneg (sourceCoefficient s ha seed I)))
    (original_coefficient_mass s ha hb seed) 2
  apply htail.trans
  calc
    _ = (∑I∈sourceColumns s,‖sourceCoefficient s ha seed I‖)^2*F := by dsimp only [F];ring
    _ ≤ (massCap s)^2*F := mul_le_mul_of_nonneg_right hmass hF
    _ = _ := by dsimp only [F];ring

end
end Candidate.Feedback.FourthPower.MixedOriginalTail
