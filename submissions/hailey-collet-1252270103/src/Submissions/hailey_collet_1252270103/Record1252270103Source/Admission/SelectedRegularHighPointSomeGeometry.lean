/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Coarse actual coordinate and canonical volume gates for the fixed HIGH caller. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedRegularHighPointSomeData
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularSourceChoice
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
namespace QRH.Record1252270103Source.Admission.SelectedRegularHighPoint
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff SchwartzMap
open CenteredMomentEnergyState CenteredMomentRetainedProfile
open Record12518109Natural Record12518109Natural.WeightedHigh
open OAI.SevenEighths.Record1252270103Source
open Set Filter HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum
open CenteredMomentCommonProfile CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice Cycle61Moment Cycle61InitialMass LocalMoment Record12518109Raw
open Cycle61Moment.LowBranch Record1252270103Second Record12518109Natural.MarkedPlain
open CenteredMomentSecondHeightFamily CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open Record1252270103Finite PhysicalAnalytic High.GlobalPhysical
open SelectedRegularSourceData SelectedHighCofactorFamily QRH.Record1252270103Low
local notation "O"=>HeckeFamily.O
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _

variable {α Label Row:Type}[Fintype α][Fintype Label]{Z:ℝ}{a:Anchor α Z}
    (F:Family a Label)(rows:Finset Row)(second:Bool)(G:Selected F Row rows second)

theorem actual_coordinate_box (θ annular wmin:ℝ)(w:α→ℝ)(T:Finset α)
    (hD:F.D=1)(hθ:0≤θ)(hθ1:θ≤1)(hreserve:F.reserve=θ)
    (ha:∀r,|F.amp (G.row r).val.1.1|≤1)
    (hω:|frequencyLoss Z 32 F.ξ+θ|≤1)
    (hV:|Real.logb Z (volume F.s)|≤1)
    (hsource:sourceRadius F.s≤Z^(2:ℝ))
    (hchild:∀r,sourceRadius (F.input (G.row r).val.1.1)≤Z^(2:ℝ))
    (hL:(G.L.absNorm:ℝ)≤Z^(4:ℝ))(hw:∀i,0≤w i)(htotal:(∑i,w i)≤1)
    (hann0:0≤annular)(hann1:annular≤1):
    ∀r i,-256≤G.x θ θ annular w wmin T r i ∧ G.x θ θ annular w wmin T r i≤256 := by
  intro r
  have hs:=FirstFamily.label_supported F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin (G.column r)
  have hf:=FirstFamily.label_common_bounds F.s F.modifier F.R F.seed (Z^F.D) Z F.ξ F.hK F.bin
    F.seed_sf F.zero₁ F.zero₂ (G.column r)
  have hc:=SelectedSecondKeyCaps.regular_common_caps F.slots F.input F.childModifier F.mask F.childSeed
    F.Hmain F.Tsec Z F.ξ ballProfile F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂)
    F.Hmain_pos F.χ₀ F.Q F.m (G.row r).val.1
  have h26:Z^(2:ℝ)≤Z^(6:ℝ):=Real.rpow_le_rpow_of_exponent_le F.hZ.le (by norm_num)
  have hforced:((G.sel r).Cf.absNorm:ℝ)≤Z^(8:ℝ):=by
    have hnorm:=SelectedForcedGeometry.norm_le_of_dvd (G.sel r).Cf (G.L^2)
      (pow_ne_zero 2 G.L_ne) (G.forced_upper r)
    rw [map_pow,Nat.cast_pow] at hnorm
    apply hnorm.trans ((pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2).trans_eq _)
    rw [←Real.rpow_mul_natCast (zero_lt_one.trans F.hZ).le]
    norm_num
  have hh:=selected_cofactor_coordinate_box F.s F.reflected second (F.first (G.row r).val.1)
    (G.datum r).C (G.datum r).D F.R (G.sel r) (G.datum r).inactive
    Z F.D (F.amp (G.row r).val.1.1) F.ξ F.reserve θ θ annular wmin 6 8 1 1 w T
    F.hZ (by norm_num) hs.1 hs.2.1 (G.datum r).hC (G.datum r).hD (G.datum r).sameSupport
    ⟨hf.2.2.1.trans (hsource.trans h26),hf.2.2.2.trans (hsource.trans h26)⟩
    ⟨hc.1.trans ((hchild r).trans h26),hc.2.trans ((hchild r).trans h26)⟩
    (by rw [hD];norm_num) (hV.trans (by norm_num)) ((ha r).trans (by norm_num))
    (by rw [hreserve];exact hω.trans (by norm_num))
    (by rw [abs_of_nonneg hθ];linarith) hforced hw htotal hann0 hann1
  intro i
  have h:=hh i
  change -256≤(G.sel r).coordinate _ _ _ _ _ _ _ _ _ _ _ _ i ∧ _≤256
  rw [abs_of_nonneg hθ] at h
  exact ⟨(show (-256:ℝ)≤-(32*6+θ+8+2*1+1) by linarith only [hθ1]).trans h.1,
    h.2.trans (show (32*6+θ+8+2*1+1:ℝ)≤256 by linarith only [hθ1])⟩

namespace Canonical
variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{hH:RayOrthogonality.globalUnits M≤H}
  {W:ℝ→ℂ}{hW:ContDiff ℝ ∞ W}{hWs:Function.support W⊆Icc (1:ℝ) 2}
  {ηanchor η₀:Character}{R₀:Ideal O}{hZ:1<Z}{s:Input α}
  (c:Canonical M H hH W hW hWs ηanchor η₀ R₀ Z hZ s)

theorem source_volume (n:Source)(b θ:ℝ)(hL:0≤(n.L:ℝ))(hθ:θ≤(n.allowance:ℝ))
    (hlo:b-θ≤∑i,c.w i)(hhi:(∑i,c.w i)≤b)
    (hadm:(globalFace (n.B:ℝ) (n.L:ℝ) (n.cap:ℝ)).Admissible
      (length Z c.X₁) (length Z c.X₂) (∑i,c.w i) 1):
    Real.logb Z (volume s)≤sourceTReal n b+b := by
  have hv:volume s≤Z^(length Z c.X₁+length Z c.X₂+∑i,c.w i):=by
    simpa only [c.input,CenteredMomentExceptionalAmplitudePair.volume,volume] using initialInput_volume_le_clipped M H hH W hW hWs Z (zero_lt_one.trans hZ) ηanchor η₀ R₀
      c.ray c.w c.v c.origin c.p (by norm_num) c.X₁ c.X₂ c.Y₁ c.Y₂ c.X₁_pos c.X₂_pos c.Y₁_pos c.Y₂_pos c.product hZ
  have hh:=Real.logb_le_logb_of_le hZ (volume_pos s) hv
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hh
  have hb:length Z c.X₁+length Z c.X₂+(n.L:ℝ)*(∑i,c.w i)≤(n.B:ℝ):=by
    simpa only [globalFace,mul_one] using hadm.2.2.2.2.2.2
  have hm:=mul_le_mul_of_nonneg_left (show b-(n.allowance:ℝ)≤∑i,c.w i by linarith) hL
  dsimp only [sourceTReal]
  linarith
end Canonical

def pointBudget (n:Source)(N J:ℕ)(θ reserve εslot wmin C Z:ℝ)(P:HighSourceParameters)
    (control:Finset (ℕ×ℕ))(s:Input α)(reflected:Bool)(bin:ℤ×(Fin 5→ℤ))
    (ξ:ℝ)(p:Profiles (1/4) (9/4)):ℝ :=
  let e:=highBuffer 1 1 εslot (θ/16)
  let annular:=3*(N:ℝ)*Real.logb Z 2
  ∑k∈High.BufferedSelectedPaidSome.highBins e (n.q:ℝ),
    (C*Z^(θ+θ)*forcedProfileCost s)*((max 1 (forcedProfileCost s))^2*(
    geometryHighFactor reflected (geometrySupportConstant N 1 (1/4) (1/4)) bin*
    cofactorRestorationCost θ 2 Z*(p.control control)^2*
    ((Finset.Icc (⌊-((256:ℝ)+5*6)/θ⌋:ℤ) ⌊((256:ℝ)+5*6)/θ⌋).card^4:ℕ)*
    (1+rawGeometryHeight Z P.τ (bufferCount e))^J*
    Z^(((1-unmarkedDensity (2*bufferValue e k-1))*(frequencyLoss Z 32 ξ+θ)+
      unmarkedDensity (2*bufferValue e k-1)*θ+θ)-((n.highFee:ℝ)+reserve)+
      (2*bufferValue e k-1)*annular+4*θ+θ+reserve/16+2*P.εplain*P.d+
      (2*P.εslot*P.d)*N+6*(θ/100))))

variable (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
    (η₀:Character)(P:HighSourceParameters)(e q θ annular wmin:ℝ)(w:α→ℝ)(T:Finset α)
    (Snew Anew:Finset (Ideal O))(hQM:F.Q≤M)(hQη:F.Q≤η₀.modulus)

def SharedState (st:rows→NaturalState Z P.Bmask P.bΦ)
    (hfixed:∀l,(st l).fixedModulus=F.Q)(keep:∀l,(st l).radial.keep (G.z l))
    (select:rows→BufferIndex e):Prop :=
  ∀l,(st l).character=G.τ l ∧
    (st l).puncture=Selection.puncture (G.sel l)*((newtonDivisorPair Snew Anew).1*(newtonDivisorPair Snew Anew).2) ∧
    (st l).width≤P.Mcap ∧
    RetainedZeroBin M H hH (st l) η₀ ((hfixed l).trans_le hQM) ((hfixed l).trans_le hQη)
      (G.z l) (keep l) e (Z^P.τ) (select l) ∧
    (bufferValue e (select l)<(q+1)/2→ActualLow M H hH (st l) η₀
      ((hfixed l).trans_le hQM) ((hfixed l).trans_le hQη) ((q+1)/2) e
      (3*((select l).1.val+1:ℕ)*Z^P.τ) (G.z l)) ∧
    1≤((st l).radial.profile (‖ConcreteTraceCRT.eisEmbedding (G.z l)‖^2/(st l).radial.scale)).re ∧
    (st l).radial.profile (‖ConcreteTraceCRT.eisEmbedding (G.z l)‖^2/(st l).radial.scale)≠0 ∧
    SelectedSecondKeyCaps.KeyCaps (G.key l) Z 6
      (Real.logb Z ((firstSourceMissing (!F.reflected) (G.key l).val.1).absNorm:ℝ)) ∧
    rawFrequencyNorm (nonzeroJointSourceRow (G.key l))≤Z^(G.x θ θ annular w wmin T l 2)

end
end QRH.Record1252270103Source.Admission.SelectedRegularHighPoint
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularHighPoint.actual_coordinate_box
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularHighPoint.Canonical.source_volume
