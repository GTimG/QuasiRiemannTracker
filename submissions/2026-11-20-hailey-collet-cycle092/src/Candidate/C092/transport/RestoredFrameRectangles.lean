/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The two original arm labels survive both actual inverse-divisor
shortenings. The reference has its own .115/.72092 rectangle. -/
import Candidate.C092.transport.RestoredFirstHitGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAddedZeroUniform CenteredMomentEnergyBands
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open QRH.SilDensitySplit.CubeFree.Second.Provider QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle090
namespace QRH.Cycle092.FixedFramePacking
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
variable {ι:Type} [Fintype ι]
local instance (priority := 2000) c092LocalInst_Candidate_C092_transport_RestoredFrameRectangles_de2c82663c3c1008_001 {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) := Classical.decEq _

theorem actual_rectangles (M:Id) [NeZero M] (Hr:Subgroup (O⧸M)ˣ)
    (hHr:RayOrthogonality.globalUnits M ≤ Hr) (r:QRH.SilDensitySplit.CubeFree.FP.RestoredRootSource.Data M Hr ι)
    (X₁ X₂ t₁ t₂ n y:ℝ) (d:IdealPair) (hd₁:d.1≠0) (hd₂:d.2≠0)
    (g:DividedLengths r.Z X₁ X₂ (r.Z^(115/1000:ℝ)) (X₁*X₂/r.Z^(115/1000:ℝ)) d)
    (hL:length r.Z X₁ ≤ n) (hS:length r.Z X₂ ≤ y) (hy:y ≤ sourceY) (hn:n ≤ sourceRatio*y) :
    let s:=dividedCanonicalSource M Hr hHr r X₁ X₂ (r.Z^(115/1000:ℝ)) (X₁*X₂/r.Z^(115/1000:ℝ)) t₁ t₂ d g
    ∀ (cover:OriginalEnclosure s) (G:Id) (B:actualAllocations (tuplePools s) G) (J:Finset (liveIndices B.val)),
    let child:=renorm (restOf s (by norm_num) cover G B J)
    child.X₁ ≤ r.Z^n ∧ child.X₂ ≤ r.Z^y ∧ child.Y₁ ≤ r.Z^(115/1000:ℝ) ∧ child.Y₂ ≤ r.Z^(72092/100000:ℝ) := by
  intro s cover G B J child
  have h0:=zero_lt_one.trans r.hZ
  have raw (X t:ℝ) (h:length r.Z X ≤ t) : X ≤ r.Z^t := calc
    X  ≤  max 1 X := le_max_right _ _
    _ = r.Z^(length r.Z X) := (Real.rpow_logb h0 r.hZ.ne' (zero_lt_one.trans_le (le_max_left _ _))).symm
    _  ≤  _ := Real.rpow_le_rpow_of_exponent_le r.hZ.le h
  have hx:=raw _ _ hL
  have hy':=raw _ _ hS
  have x1:0<X₁:=(div_pos_iff_of_pos_right (nrm_pos hd₁)).mp g.x₁
  have x2:0<X₂:=(div_pos_iff_of_pos_right (nrm_pos hd₂)).mp g.x₂
  have hq:=Real.rpow_pos_of_pos h0 (115/1000:ℝ)
  have href: X₁*X₂/r.Z^(115/1000:ℝ) ≤ r.Z^(72092/100000:ℝ) := calc
    _  ≤  (r.Z^n*r.Z^y)/r.Z^(115/1000:ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul hx hy' x2.le (Real.rpow_nonneg h0.le _)) hq.le
    _ = r.Z^(n+y-115/1000) := by rw [←Real.rpow_add h0,←Real.rpow_sub h0]
    _  ≤  _ := Real.rpow_le_rpow_of_exponent_le r.hZ.le (by norm_num [sourceY,sourceRatio] at hy hn;linarith)
  have dec (x d':ℝ) (hx:0 ≤ x) (hd:1 ≤ d') : x/d' ≤ x := div_le_self hx hd
  have h₁:=nrm_one_le (restOf s (by norm_num) cover G B J).hd.1
  have h₂:=nrm_one_le (restOf s (by norm_num) cover G B J).hd.2
  exact ⟨(dec _ _ g.x₁.le h₁).trans ((dec _ _ x1.le (nrm_one_le hd₁)).trans hx),
    (dec _ _ g.x₂.le h₂).trans ((dec _ _ x2.le (nrm_one_le hd₂)).trans hy'),
    (dec _ _ g.y₁.le h₁).trans (dec _ _ hq.le (nrm_one_le hd₁)),
    (dec _ _ g.y₂.le h₂).trans ((dec _ _ (div_nonneg (mul_nonneg x1.le x2.le) hq.le) (nrm_one_le hd₂)).trans href)⟩

#print axioms actual_rectangles
end QRH.Cycle092.FixedFramePacking
