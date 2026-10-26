/- Consume genuine recursive LOW and separately marked root HIGH in the actual native parent budget.
Original parent proof Hailey Collet; root-source assembly Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.RegionalParentBudget
import Candidate.Research.RecursiveAffine.RootLedgerBinding
import Candidate.Research.RecursiveAffine.MarkedRootHigh.RootAffine

noncomputable local instance actualRootPaidLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 7000
namespace OAI.SevenEighths.Cycle153RootInitialAssembly
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open Cycle63Moment Cycle63Moment.LowBranch ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open CenteredMomentNaturalFixedRaySource CenteredMomentAllocatedRayDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands Cycle63InitialSource
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondHeightFamily
open Cycle63InitialMass Cycle153RegionalLow Cycle153ParentMass CenteredMomentSourceMass
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance rootPaidFinite : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- LOW is the actual recursive selected source with return Z^(amp−3δ).
The separately marked HIGH has its native return KH Z^(amp+target).
The parent radial width, first-mass normalizer and prime average stay in the
native budget. This theorem assumes neither an initial moment nor a class bound. -/
theorem actual_root_parent_budget_from_sources
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
    (SH : Finset (ℕ×ℕ)) (dh : ℕ) (KH : ℝ) (hKH : 0≤KH)
    (hreserve : 128*g.μ≤Cycle63.AffineLedger.lowReserve) :
    ∃(S : Finset (ℕ×ℕ))(D : ℕ)(Croot : ℝ),SH⊆S ∧ dh ≤ D ∧ 0<Croot ∧
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
    let EL:=Z^(Cycle63.AffineLedger.amp beta-3*g.δ);
    (∀(hfit' : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ) ≤ 1+g.μ/16)
      (hwL : ∀j,w j ≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))(hwr : ∀j,w j/31 ≤ 1),
      RegionalLowSelectedAt M H hH W hβlo g 2
        (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs (fun _ _ _=>True)
        (fun _ _ _ _ _=>True) Sp degreeAll Kall η₀ Q hQM hQ72 Z EL
        hZ s p caps θ w σ freq hmatch R 1 Bmask Mrow hR squarefree_one hBmask20 hRcap hMrow hMrow1
        hfit' trivial height mesh hw hwL hwr hmesh0 hwm hσ hheight hfreq hT hβhi hzslot haff) →
    let EH:=KH*Z^(Cycle63.AffineLedger.amp beta+Cycle153RootHigh.geometryAffineHighTarget g.μ g.δ);
      GeometryAffineHighGiven (α:=T) M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT (1/4) (9/4) s p R 1 Mrow
        (Cycle63.AffineLedger.amp beta) Ψ caps.zero₁ caps.zero₂ SH dh height EH →
    ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ)),
      key∈commonGeometryBins s R 1 (Z^Mrow) Z (geometryLossUnit 1 εaffine/64) →
    ∀firstHeight : ℝ,
      geometryLiveBudget reflected s R 1 (Z^Mrow) Z (geometryLossUnit 1 εaffine/64) Mrow
        (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow) key
        (fun q=>normPhase (coordinateBlock s R 1 Ψ (Z^Mrow) Z (geometryLossUnit 1 εaffine/64) q))
        (Fintype.card T) (9/4) firstHeight ≤
      Croot*geometryHighFactor reflected 64 key*(p.control S)^2*(1+|s.t|+height)^D*
        (1+‖firstHeight‖)^D*Z^(1-Mrow) := by
  obtain ⟨S,D,Cb,Chigh,hSH,hdh,hCb,hChigh,hbudget⟩:=actual_regional_parent_paid_budget
    M H hH T Sbad hbad W hW hWs hβlo hβhi g εaffine mesh Bmask hε hmesh hmesh0 hμ hδ
    hBmask hBmask20 hmeshcap Ψ η₀ Q hQM hQ hQt hQ72 Cs hCs Sp degreeAll Kall hKall SH dh
  let Croot:=1+Cb+Chigh*(1+KH)
  have hCroot : 0<Croot := by dsimp [Croot];positivity
  refine ⟨S,D,Croot,hSH,hdh,hCroot,?_⟩
  filter_upwards [hbudget] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ hT s p caps θ w σ freq hmatch hcolumns R Mrow hR hRcap hMrow hMrow1 hfit
    height hw hwm hσ hheight hfreq hzslot haff beta hbeta EL hlow EH hhigh reflected key hkey firstHeight
  have hZ0 : 0<Z:=zero_lt_one.trans hZ
  have hEL : 0≤EL:=Real.rpow_nonneg hZ0.le _
  have hEH : 0≤EH:=mul_nonneg hKH (Real.rpow_nonneg hZ0.le _)
  have hb:=hz.2 hZ hT s p caps θ w σ freq hmatch hcolumns R Mrow hR hRcap hMrow hMrow1 hfit
    height hw hwm hσ hheight hfreq hzslot haff beta hbeta EL hEL hlow EH hEH hhigh reflected key hkey firstHeight
  have ht : 3*g.δ+Cycle153RootHigh.geometryAffineHighTarget g.μ g.δ≤0 := by
    have hr : 128*g.μ≤Cycle153.MarkedRootPrice.lowReserve:=hreserve
    dsimp [Cycle153RootHigh.geometryAffineHighTarget]
    linarith [g.μ_pos]
  have hpaid : Z^(3*g.δ-Cycle63.AffineLedger.amp beta)*(EL+EH)≤1+KH := by
    dsimp only [EL,EH]
    rw [mul_add]
    have he : Z^(3*g.δ-Cycle63.AffineLedger.amp beta)*
        Z^(Cycle63.AffineLedger.amp beta-3*g.δ)=1 := by
      rw [←Real.rpow_add hZ0]
      convert Real.rpow_zero Z using 1 <;> ring
    rw [he]
    have hh : Z^(3*g.δ-Cycle63.AffineLedger.amp beta)*
        (KH*Z^(Cycle63.AffineLedger.amp beta+Cycle153RootHigh.geometryAffineHighTarget g.μ g.δ))=
        KH*Z^(3*g.δ+Cycle153RootHigh.geometryAffineHighTarget g.μ g.δ) := by
      rw [mul_left_comm,←Real.rpow_add hZ0]
      congr 2 <;> ring
    rw [hh]
    simpa only [mul_one,add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left
      ((Real.rpow_le_rpow_of_exponent_le hZ.le ht).trans_eq (Real.rpow_zero Z)) hKH) 1
  have hret : Z^(-geometryAffineParentSaving+(1-Mrow))≤Z^(1-Mrow):=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith [geometryAffineParentSaving_pos])
  have hunit : 1≤Z^(1-Mrow):=Real.one_le_rpow hZ.le (by linarith)
  have hbracket : Cb*Z^(-geometryAffineParentSaving+(1-Mrow))+
      Chigh*Z^(3*g.δ-Cycle63.AffineLedger.amp beta)*(EL+EH)≤Croot*Z^(1-Mrow) := by
    calc
      _ ≤ Cb*Z^(1-Mrow)+Chigh*(1+KH) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hret hCb)
          (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpaid hChigh)
      _ ≤ (Cb+Chigh*(1+KH))*Z^(1-Mrow) := by
        have hh:=mul_le_mul_of_nonneg_left hunit (mul_nonneg hChigh (by linarith : 0≤1+KH))
        nlinarith only [hh]
      _ ≤ Croot*Z^(1-Mrow) := by
        exact mul_le_mul_of_nonneg_right (by dsimp [Croot];linarith) (Real.rpow_nonneg hZ0.le _)
  apply hb.trans
  have hh:=mul_le_mul_of_nonneg_left hbracket
    (show 0≤1*geometryHighFactor reflected 64 key*(p.control S)^2*(1+|s.t|+height)^D*(1+‖firstHeight‖)^D by
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_one
        (geometry_high_factor_pos reflected 64 key (by norm_num)).le) (sq_nonneg _))
        (pow_nonneg (by positivity) _)) (pow_nonneg (by positivity) _))
  convert hh using 1 <;> ring

end
end OAI.SevenEighths.Cycle153RootInitialAssembly
#print axioms OAI.SevenEighths.Cycle153RootInitialAssembly.actual_root_parent_budget_from_sources
