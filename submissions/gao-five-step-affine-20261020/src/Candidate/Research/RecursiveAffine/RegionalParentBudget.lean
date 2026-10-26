/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineParentBudget
import Candidate.Research.RecursiveAffine.RegionalParentBranches
import Candidate.Research.RecursiveAffine.RegionalMainDriver
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineAtState
import Candidate.Cycle63.Physical.InitialMass.GeometryAffinePaidAssembly
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorFamily
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineErrorCompletePayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineFinalWeight
import Candidate.Cycle63.Physical.InitialMass.CommonMeshMask

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153ParentMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle63Moment
open Cycle63Moment.LowBranch
open ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open Cycle63InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentAllocatedRayDictionary CenteredMomentSourceMass CenteredMomentFirstSourceReduction
open CenteredMomentSecondHeightFamily
open Cycle63InitialMass Cycle153RegionalLow Cycle153RegionalMain

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance affineParentBudgetFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

variable [Cycle63.AffineLedger] in
/-- The retained budget of a parent `s` with puncture `R`, seed one and radial scale `Z^Mrow`, over the slot subset `T`:
the zero term, the paid LOW part of the main branch (the selected low frequency columns of row 5, given at `Sp`,
`degreeAll` and `Kall`), the given HIGH part (`GeometryAffineHighGiven`, linear in `EH`) and the paid error branch
are joined to a bound with one profile union `S`, one height degree `D` and the constants `Cb` and `Chigh`. -/
theorem actual_regional_parent_paid_budget
    (T : Finset α) (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (g : GeometryAffineLowSchedule) (εaffine mesh Bmask : ℝ) (hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2) (hmesh0 : 0 ≤  mesh)
    (hμ : g.μ=geometryLossUnit 1 εaffine)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 130 (3*((Fintype.card α:ℝ)+2)) (Fintype.card α))
    (hBmask : 0 ≤ Bmask) (hBmask20 : Bmask ≤ 20)
    (hmeshcap : mesh ≤ Cycle25.Energy.commonMesh 2 (28+Bmask) 1 (g.μ/8))
    (Ψ : 𝓢(ℝ,ℂ)) (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (hQ : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤) (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})
    (Cs : ℝ) (hCs : 1 ≤ Cs) (Sp : Finset (ℕ×ℕ)) (degreeAll : ℕ) (Kall : ℝ) (hKall : 0 ≤ Kall)
    (SH : Finset (ℕ×ℕ)) (dh : ℕ) :
    ∃(S : Finset (ℕ×ℕ))(D : ℕ)(Cb Chigh : ℝ),SH⊆S ∧ dh ≤ D ∧ 0 ≤ Cb ∧ 0 ≤ Chigh ∧
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀(hZ : 1<Z)(hT : 2<Z^g.τ)(s : Input T)(p : Profiles (1/4) (9/4))
      (caps : GeometryAffineLowSourceGates s p Cs Z)(θ : T→RayQuotient.Characters M H)(w σ freq : T→ℝ),
      ∀hmatch : Matches M H hH s η₀ θ w σ freq W 2 Z,
      (∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ) ≤ Z^(3:ℝ)) →
    ∀(R : Ideal O)(Mrow : ℝ)(hR : R≠0)(hRcap : (R.absNorm:ℝ) ≤ Z^Bmask)
      (hMrow : 0 ≤ Mrow)(hMrow1 : Mrow ≤ 1),
      Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ) ≤ 1+geometryLossUnit 1 εaffine/16 →
    ∀(height : ℝ)(hw : ∀j,0 ≤ w j)(hwm : ∀j,w j ≤ mesh)
      (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))(hheight : 0 ≤ height)(hfreq : ∀j,|freq j| ≤ height)
      (hzslot : Cycle63.AffineLedger.slotFloor ≤ ∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j)) ≤ Cycle63.AffineLedger.slotTop)
      (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j)) ≤
        Cycle63.AffineLedger.B),
    ∀beta : ℝ,beta=Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))) →
    ∀(EL : ℝ),0 ≤ EL →
    (∀(hfit' : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ) ≤ 1+g.μ/16)
      (hwL : ∀j,w j ≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))(hwr : ∀j,w j/31 ≤ 1),
      RegionalLowSelectedAt M H hH W hβlo g 2
        (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs (fun _ _ _=>True)
        (fun _ _ _ _ _=>True) Sp degreeAll Kall η₀ Q hQM hQ72 Z EL
        hZ s p caps θ w σ freq hmatch R 1 Bmask Mrow hR squarefree_one hBmask20 hRcap hMrow hMrow1
        hfit' trivial height mesh hw hwL hwr hmesh0 hwm hσ hheight hfreq hT hβhi hzslot haff) →
    ∀EH : ℝ,0 ≤ EH →
      GeometryAffineHighGiven (α:=T) M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT (1/4) (9/4) s p R 1 Mrow
        (Cycle63.AffineLedger.amp beta) Ψ caps.zero₁ caps.zero₂ SH dh height EH →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
      key∈commonGeometryBins s R 1 (Z^Mrow) Z (geometryLossUnit 1 εaffine/64) →
    ∀firstHeight : ℝ,
      geometryLiveBudget reflected s R 1 (Z^Mrow) Z (geometryLossUnit 1 εaffine/64) Mrow
        (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key
        (fun q=>normPhase (coordinateBlock s R 1 Ψ (Z^Mrow) Z (geometryLossUnit 1 εaffine/64) q))
        (Fintype.card T) (9/4) firstHeight ≤
      1*geometryHighFactor reflected 64 key*(p.control S)^2*(1+|s.t|+height)^D*(1+‖firstHeight‖)^D*
        (Cb*Z^(-geometryAffineParentSaving+(1-Mrow))+
          Chigh*Z^(3*g.δ-Cycle63.AffineLedger.amp beta)*(EL+EH)) := by
  have hμ0:=g.μ_pos
  have hmeshμ : mesh ≤ g.μ/8 :=
    hmeshcap.trans (Cycle25.Energy.commonMesh_le 2 (28+Bmask) 1 (g.μ/8) (by norm_num) (by linarith)
      (by linarith))
  have hmeshcap' : mesh ≤ Cycle25.Energy.commonMesh 2 (28+Bmask) 1 (geometryLossUnit 1 εaffine/8) := by
    rwa [hμ] at hmeshcap
  have hmeshμ' : mesh ≤ geometryLossUnit 1 εaffine/8 := by rwa [hμ] at hmeshμ
  have hμpos' : 0<geometryLossUnit 1 εaffine := by rw [←hμ]; exact hμ0
  have hμcap' : geometryLossUnit 1 εaffine ≤ 1/128 := by rw [←hμ]; exact g.μ_cap
  obtain ⟨Cr,hCr,hret⟩:=actual_affine_geometry_parent_retained_budget (α:=α) M H hH Sbad hbad W g.δ mesh
    (geometryLossUnit 1 εaffine) g.δ_pos hμpos' hμcap' hmesh Cs hCs
  obtain ⟨Ksel,hKsel,Cm,hCm,Chigh,hChigh,SE,dE,hmain⟩:=actual_affine_main_parent_component_payment_with_regional_returns
    (α:=α) M H hH 0 degreeAll dh logAnnulus_compact logAnnulus_smooth Sbad hbad W εaffine mesh hε hmesh g hμ
    (Fintype.card α) le_rfl 130 (3*((Fintype.card α:ℝ)+2)) (by norm_num) (by positivity) hδ hmeshμ
    (internalQ Q η₀) hQ hQt hQ72 Kall hKall Cs hCs
  obtain ⟨degree,windowDegree,dN,SN,Cn,hCn,hnormT⟩:=actual_affine_error_normalized_parent_family (α:=α) M H hH
    Sbad hbad W hW hWs hβlo Ψ η₀ Q hQM hQ hQt hQ72 εaffine mesh Bmask Cs hε hmesh0 hmesh hmeshμ' hBmask
    hmeshcap' hCs T
  obtain ⟨Se,De,Ce,hCe,herr⟩:=actual_affine_error_complete_parent_payment (α:=α) M H hH T 0 degree windowDegree
    dN logAnnulus_compact logAnnulus_smooth Sbad hbad W Ψ η₀ εaffine mesh Bmask Cs hε hmesh hBmask20
    (internalQ Q η₀) hQ hQt hQ72 SN Cn hCn hnormT
  let Sm : Finset (ℕ×ℕ):=SE∪Sp
  let Dm : ℕ:=max dE degreeAll
  let SHall : Finset (ℕ×ℕ):=Sm∪SH
  let dhall : ℕ:=max Dm dh
  refine ⟨(({(0,0)}∪Sm)∪Se)∪SHall,max (max Dm De) dhall,Cr+Cm+Ce,Chigh,
    (Finset.subset_union_right (s₁:=Sm) (s₂:=SH)).trans Finset.subset_union_right,
    (le_max_right Dm dh).trans (le_max_right _ _),by linarith,hChigh,?_⟩
  filter_upwards [hmain,hret,herr,eventual_geometry_small_frequency g.μ g.μ_pos] with Z hm hr he hf
  refine ⟨hr.1,?_⟩
  intro hZ hT s p caps θ w σ freq hmatch hcolumns R Mrow hR hRcap hMrow hMrow1 hfit height hw hwm hσ hheight
    hfreq hzslot haff beta hbeta EL hEL hlow EH hEH hhigh reflected key hkey firstHeight
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hRcap20 : (R.absNorm:ℝ) ≤ Z^(20:ℝ) :=
    hRcap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hBmask20)
  have hwL : ∀j,w j ≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8) := fun j=>
    (hwm j).trans (hmeshcap.trans (Cycle25.Energy.commonMesh_anti_mask 2 1 (g.μ/8) (by norm_num)
      (B₁:=28) (B₂:=28+Bmask) (by norm_num) (by linarith) (by linarith)))
  have hcol : ∀v : (T⊕Fin 2)→Ideal O,(∀j,v j∈s.pools j)→
      ((CenteredMomentAddedZeroUniform.finiteTupleProduct v).absNorm:ℝ) ≤ Z^(3:ℝ) := by
    intro v hv
    apply hcolumns
    simp only [finiteColumns,Finset.mem_image,Fintype.mem_piFinset]
    exact ⟨v,hv,rfl⟩
  let capsE : GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z :=
    caps.toGeometryAffineExceptionalSourceGates
  obtain ⟨hne,hpool,hall⟩:=hr.2 hZ T s p capsE η₀ θ w σ freq hmatch hcol R 1 Mrow hR squarefree_one hRcap20
    hMrow hMrow1 hwm hzslot haff beta hbeta
  obtain ⟨υ,hυ,hbudget⟩:=hall reflected key Ψ firstHeight
  have hside : 0 ≤ geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key :=
    (geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)).le
  have hCH : 0 ≤ EH*(p.control SH)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^dh :=
    mul_nonneg (mul_nonneg (mul_nonneg hEH (sq_nonneg _)) hside) (pow_nonneg (by positivity) _)
  have hfit' : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ) ≤ 1+g.μ/16 := by rw [hμ]; exact hfit
  have hkey' : key∈commonGeometryBins s R 1 (Z^Mrow) Z (g.μ/64) := by rw [hμ]; exact hkey
  have hbranches:=actual_regional_parent_selected_branches M H hH W hβlo hβhi g Cs Sp degreeAll Kall hKall η₀ Q
    hQM hQ72 Z hZ hT s p caps θ w σ freq hmatch R Bmask Mrow hR hBmask20 hRcap hMrow hMrow1 hfit' height
    mesh hw hwL hmesh0 hwm hσ hheight hfreq hzslot haff hf.2 beta hbeta reflected firstHeight key Ψ 1
    (EH*(p.control SH)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^dh) hCH dh
    (hhigh reflected key hkey' firstHeight 1) Kall Sm Dm degreeAll dh le_rfl Finset.subset_union_right
    (le_max_right _ _) le_rfl le_rfl EL hEL (hlow hfit' hwL)
  have hmainB:=hm.2 hZ T s p capsE η₀ θ w σ freq hmatch R 1 Mrow hR squarefree_one hRcap20 hMrow hMrow1 hfit'
    hwm hzslot haff beta hbeta Sm Dm Finset.subset_union_left (le_max_left _ _) Ψ reflected key firstHeight
    height hheight 1 (EL*((p.control Sm)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^Dm))
    (EH*(p.control SH)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^dh) (by positivity) hCH hbranches
  rw [hμ] at hmainB
  have herrB:=he.2 hZ s p capsE caps.b₁ caps.b₂ caps.plainScales caps.windows θ w σ freq hmatch R 1 Mrow hR
    squarefree_one hRcap hMrow hMrow1 hfit hw hwm hσ hzslot haff beta hbeta reflected key firstHeight height
    hheight hfreq υ hυ
  have hsaving:=geometryAffineParentSaving_pos
  have hlow2 : 0<Cycle63.AffineLedger.lowReserve := Cycle63.AffineLedger.lowReserve_pos
  have hs1 : geometryAffineParentSaving ≤ Cycle63.AffineLedger.zeroSaving := min_le_left _ _
  have hs2 : geometryAffineParentSaving ≤ Cycle63.AffineLedger.lowReserve/4 := min_le_right _ _
  have hretControl :
      EL*((p.control Sm)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^Dm)+
      EH*(p.control SH)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^dh  ≤
      (EL+EH)*(p.control SHall)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^dhall := by
    have hSm:=Cycle63Physical.profile_control_mono p (Finset.subset_union_left (s₁:=Sm) (s₂:=SH))
    have hSH:=Cycle63Physical.profile_control_mono p (Finset.subset_union_right (s₁:=Sm) (s₂:=SH))
    have hx : 1 ≤ 1+|firstHeight|+height := by linarith [abs_nonneg firstHeight]
    have hmPow:=pow_le_pow_right₀ hx (le_max_left Dm dh)
    have hhPow:=pow_le_pow_right₀ hx (le_max_right Dm dh)
    have hSmSq := pow_le_pow_left₀ (p.control_nonneg Sm) hSm 2
    have hSHSq := pow_le_pow_left₀ (p.control_nonneg SH) hSH 2
    have hSmCtrl := mul_le_mul (mul_le_mul_of_nonneg_right hSmSq hside) hmPow
      (pow_nonneg (by linarith : 0 ≤ 1+|firstHeight|+height) Dm)
      (mul_nonneg (sq_nonneg (p.control (Sm∪SH))) hside)
    have hSHCtrl := mul_le_mul (mul_le_mul_of_nonneg_right hSHSq hside) hhPow
      (pow_nonneg (by linarith : 0 ≤ 1+|firstHeight|+height) dh)
      (mul_nonneg (sq_nonneg (p.control (Sm∪SH))) hside)
    calc
      _  ≤  EL*((p.control SHall)^2*geometryHighFactor reflected
            (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^dhall)+
          EH*(p.control SHall)^2*geometryHighFactor reflected
            (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^dhall := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hSmCtrl hEL
        · simpa only [mul_assoc,SHall,dhall] using mul_le_mul_of_nonneg_left hSHCtrl hEH
      _ = _ := by ring
  have hmainUp:=hmainB.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hretControl (by positivity)))
  have hjoined:=affine_parent_paid_budget_of_components p Sm Se SHall Dm De dhall _ _ _ _ _ Cr Cm Ce Chigh (EL+EH)
    (geometryHighFactor reflected (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key) s.t firstHeight
    height (Z^(-(Cycle63.AffineLedger.zeroSaving:ℝ)+(1-Mrow)))
    (Z^(-((Cycle63.AffineLedger.lowReserve/2):ℝ)+(1-Mrow)))
    (Z^(-((Cycle63.AffineLedger.lowReserve/4):ℝ)+(1-Mrow))) (Z^(3*g.δ-Cycle63.AffineLedger.amp beta))
    (Z^(-geometryAffineParentSaving+(1-Mrow))) ((1:Ideal O).absNorm:ℝ) hCr.le hCm hCe hChigh (add_nonneg hEL hEH) hside hheight
    (by simp) (Real.rpow_nonneg hZ0.le _) (Real.rpow_nonneg hZ0.le _) (Real.rpow_nonneg hZ0.le _)
    (Real.rpow_nonneg hZ0.le _)
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)) (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)) hbudget
    (by simpa only [mul_assoc] using hmainUp) (by simpa only [mul_assoc] using herrB)
  simp only [geometry_affine_support_constant] at hjoined
  exact hjoined


variable [Cycle63.AffineLedger] in
/-- The normalized physical mass of a parent `s` with puncture `R`, seed one and radial scale `Z^Mrow`, over the slot subset
`T`, is at most the sum of a term of the old size `Z^(1 + εbin)` and a term linear in the real `EH` that bounds the HIGH part
of the second transform, with one profile union `S` and one height degree `D`. -/
theorem actual_regional_parent_mass
    (T : Finset α) (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100 ≤ HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (g : GeometryAffineLowSchedule) (εaffine mesh Bmask : ℝ) (hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2) (hmesh0 : 0 ≤  mesh)
    (hμ : g.μ=geometryLossUnit 1 εaffine)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 130 (3*((Fintype.card α:ℝ)+2)) (Fintype.card α))
    (hBmask : 0 ≤ Bmask) (hBmask20 : Bmask ≤ 20)
    (hmeshcap : mesh ≤ Cycle25.Energy.commonMesh 2 (28+Bmask) 1 (g.μ/8))
    (Ψ : 𝓢(ℝ,ℂ)) (η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (hQ : internalQ Q η₀≠0) (hQt : internalQ Q η₀≠⊤) (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})
    (Cs : ℝ) (hCs : 1 ≤ Cs) (Sp : Finset (ℕ×ℕ)) (degreeAll : ℕ) (Kall : ℝ) (hKall : 0 ≤ Kall)
    (SH : Finset (ℕ×ℕ)) (dh : ℕ) (εbin : ℝ) (hεbin : 0<εbin) :
    ∃(S : Finset (ℕ×ℕ))(D : ℕ)(Cmain Chigh : ℝ),SH⊆S ∧ dh ≤ D ∧ 0 ≤ Cmain ∧ 0 ≤ Chigh ∧
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀(hZ : 1<Z)(hT : 2<Z^g.τ)(s : Input T)(p : Profiles (1/4) (9/4))
      (caps : GeometryAffineLowSourceGates s p Cs Z)(θ : T→RayQuotient.Characters M H)(w σ freq : T→ℝ),
      ∀hmatch : Matches M H hH s η₀ θ w σ freq W 2 Z,
      (∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ) ≤ Z^(3:ℝ)) →
    ∀(R : Ideal O)(Mrow : ℝ)(hR : R≠0)(hRcap : (R.absNorm:ℝ) ≤ Z^Bmask)
      (hMrow : 0 ≤ Mrow)(hMrow1 : Mrow ≤ 1),
      Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ) ≤ 1+geometryLossUnit 1 εaffine/16 →
    ∀(height : ℝ)(hw : ∀j,0 ≤ w j)(hwm : ∀j,w j ≤ mesh)
      (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))(hheight : 0 ≤ height)(hfreq : ∀j,|freq j| ≤ height)
      (hzslot : Cycle63.AffineLedger.slotFloor ≤ ∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j)) ≤ Cycle63.AffineLedger.slotTop)
      (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j)) ≤
        Cycle63.AffineLedger.B),
    ∀beta : ℝ,beta=Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))) →
    ∀(EL : ℝ),0 ≤ EL →
    (∀(hfit' : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ) ≤ 1+g.μ/16)
      (hwL : ∀j,w j ≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))(hwr : ∀j,w j/31 ≤ 1),
      RegionalLowSelectedAt M H hH W hβlo g 2
        (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs (fun _ _ _=>True)
        (fun _ _ _ _ _=>True) Sp degreeAll Kall η₀ Q hQM hQ72 Z EL
        hZ s p caps θ w σ freq hmatch R 1 Bmask Mrow hR squarefree_one hBmask20 hRcap hMrow hMrow1
        hfit' trivial height mesh hw hwL hwr hmesh0 hwm hσ hheight hfreq hT hβhi hzslot haff) →
    ∀EH : ℝ,0 ≤ EH →
      GeometryAffineHighGiven (α:=T) M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT (1/4) (9/4) s p R 1 Mrow
        (Cycle63.AffineLedger.amp beta) Ψ caps.zero₁ caps.zero₂ SH dh height EH →
      physicalMass s R 1 fixedBadMask 1 Ψ (Z^Mrow) Z (geometryLossUnit 1 εaffine/64)/volume s ≤
        (Cmain*Z^(1+εbin)+Chigh*Z^(Mrow+3*g.δ-Cycle63.AffineLedger.amp beta+εbin)*(EL+EH))*
          ((p.control S)^2*(1+|s.t|+height)^D) := by
  obtain ⟨S,D,Cb,Chigh,hSH,hdh,hCb,hChigh,hbud⟩:=actual_regional_parent_paid_budget (α:=α) M H hH T Sbad hbad W
    hW hWs hβlo hβhi g εaffine mesh Bmask hε hmesh hmesh0 hμ hδ hBmask hBmask20 hmeshcap Ψ η₀ Q hQM hQ hQt
    hQ72 Cs hCs Sp degreeAll Kall hKall SH dh
  have hξ : 0 ≤ geometryLossUnit 1 εaffine/64 := by
    have := geometry_loss_unit_pos 1 εaffine (by norm_num) hε
    positivity
  obtain ⟨Cmass,hCmass,hmass⟩:=uniform_geometry_parent_mass (α:=α) Ψ D D (geometryLossUnit 1 εaffine/64) εbin
    hξ hεbin logAnnulus_compact logAnnulus_smooth
  let Cconst : ℝ:=Cmass*((9/4:ℝ)^(Fintype.card α)*(1+2*(64:ℝ)^2)*(1+|2*Real.pi|)^D)
  have hCconst : 0<Cconst := by positivity
  refine ⟨S,D+D,Cconst*Cb,Cconst*Chigh,hSH,hdh.trans (Nat.le_add_right _ _),by positivity,by positivity,?_⟩
  filter_upwards [hbud,hmass] with Z hb hmZ
  refine ⟨hb.1,?_⟩
  intro hZ hT s p caps θ w σ freq hmatch hcolumns R Mrow hR hRcap hMrow hMrow1 hfit height hw hwm hσ hheight
    hfreq hzslot haff beta hbeta EL hEL hlow EH hEH hhigh
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hsaving:=geometryAffineParentSaving_pos
  have hY : 0 ≤ Cb*Z^(-geometryAffineParentSaving+(1-Mrow))+
      Chigh*Z^(3*g.δ-Cycle63.AffineLedger.amp beta)*(EL+EH) :=
    add_nonneg (mul_nonneg hCb (Real.rpow_nonneg hZ0.le _))
      (mul_nonneg (mul_nonneg hChigh (Real.rpow_nonneg hZ0.le _)) (add_nonneg hEL hEH))
  let Y : ℝ:=Cb*Z^(-geometryAffineParentSaving+(1-Mrow))+Chigh*Z^(3*g.δ-Cycle63.AffineLedger.amp beta)*(EL+EH)
  let E : ℝ:=(9/4:ℝ)^(Fintype.card α)*1*(1+2*(64:ℝ)^2)*(1+|2*Real.pi|)^D*(p.control S)^2*
    (1+|s.t|+height)^(D+D)*Y
  have hE : 0 ≤ E := by
    have hh : 0 ≤ 1+|s.t|+height := by positivity
    positivity
  have hcard : Fintype.card T ≤ Fintype.card α :=
    Fintype.card_le_of_injective (fun i : T=>i.val) Subtype.val_injective
  have hmassE:=hmZ hZ T s R 1 Mrow (Fintype.card α) (1/4) (9/4) E (by norm_num) hcard
    (by rw [caps.lower]; norm_num) caps.endpoints.1 squarefree_one hMrow caps.zero₁ caps.zero₂ caps.sourceCap
    caps.volume hE geometryDCompensator (fun key _=>geometryDCompensator_pos key) (by
      intro key hkey reflected t u
      have hbound:=hb.2 hZ hT s p caps θ w σ freq hmatch hcolumns R Mrow hR hRcap hMrow hMrow1 hfit height hw
        hwm hσ hheight hfreq hzslot haff beta hbeta EL hEL hlow EH hEH hhigh reflected key hkey
        (s.t+2*Real.pi*(u-(if reflected then -t else t)))
      exact geometry_affine_parent_final_budget_weight T s R 1 Z Mrow (geometryLossUnit 1 εaffine/64) 1
        ((p.control S)^2) height Y hZ D D Ψ reflected key t u zero_le_one (sq_nonneg _) hheight hY hbound)
  refine hmassE.trans ?_
  have hz1 : Z^(-geometryAffineParentSaving+(1-Mrow))*Z^(Mrow+εbin) ≤ Z^(1+εbin) := by
    rw [←Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hz2 : Z^(3*g.δ-Cycle63.AffineLedger.amp beta)*Z^(Mrow+εbin)=
      Z^(Mrow+3*g.δ-Cycle63.AffineLedger.amp beta+εbin) := by
    rw [←Real.rpow_add hZ0]
    congr 1
    ring
  have hctrl : 0 ≤ (p.control S)^2*(1+|s.t|+height)^(D+D) := by
    have hh : 0 ≤ 1+|s.t|+height := by positivity
    positivity
  have hmain : Cmass*E*Z^(Mrow+εbin)=
      ((Cconst*Cb)*(Z^(-geometryAffineParentSaving+(1-Mrow))*Z^(Mrow+εbin))+
        (Cconst*Chigh)*(Z^(3*g.δ-Cycle63.AffineLedger.amp beta)*Z^(Mrow+εbin))*(EL+EH))*
          ((p.control S)^2*(1+|s.t|+height)^(D+D)) := by
    dsimp only [E,Y,Cconst]
    ring
  rw [hmain,hz2]
  have hCb' : 0 ≤ Cconst*Cb := by positivity
  exact mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left hz1 hCb') le_rfl) hctrl

end
end OAI.SevenEighths.Cycle153ParentMass

#print axioms OAI.SevenEighths.Cycle153ParentMass.actual_regional_parent_paid_budget
#print axioms OAI.SevenEighths.Cycle153ParentMass.actual_regional_parent_mass
