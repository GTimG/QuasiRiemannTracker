import Candidate.Cycle62.Marked.WholeNaturalBatch
import Candidate.Cycle62.Marked.WholeFamilyMaximum
import Candidate.Cycle62.Marked.Route.ActualMaxWeighted

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle62MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open ProbeHighRowFamily LocalMoment Cycle62Moment HeckeDetectorFiberPartition
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentDetectorEnergyInitialState
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def wholeCleanFamily (η η₀ : Character) (u : FreeRow) : WholeSourceIndex M H→Character :=
  fun j=>(naturalRow (cleanWholeBase M H hH η η₀ j) u.val u.property.1).character

def wholeCleanSlot {Slot : Type} (η η₀ : Character) (W : ℝ→ℂ) (U : ℝ)
    (w σ v : Slot→ℝ) (t : FreeRow→ℝ) (θ : Slot→RayQuotient.Characters M H)
    (u : FreeRow) (s : Slot) : ℂ :=
  naturalSlot (naturalRow (excluded η (wholeAnchorMask M H hH η₀)) u.val u.property.1).character
    (primePool M H 2 (U^(w s)))
    (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
      HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (t u+v s) I) (U^(w s))

/-- The actual whole geometric zero family supplies both buffered gates of
marked max-product counting. No moment or detector-witness estimate is assumed. -/
theorem actual_whole_max_weighted {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (η η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (hbadM : ∀j,bad j≤M)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≤Ideal.span {(72:O)})
    (setup : DensityCountingSetup) (W : ℝ→ℂ) (lo hi bΦ Δ εm binWidth ηloss : ℝ)
    (dmin dmax τ ε e κw ηw : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*ηw)
    (hε : 0<ε) (hεsmall : ε≤1/1000) (he : 0<e) (he' : e<1/1000)
    (hκw : 0<κw) (hκw' : κw≤1) (hηw : 0≤ηw)
    (hbudget : 12*e*((22:ℝ)+2)+8*κw+2*ηw≤ε/2)
    (hWs : Function.support W⊆Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (hbΦ : 0<bΦ) (hrad : Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ)
    (hbin : 0<binWidth) (hη : 0<ηloss)
    (hΔ0 : 0≤Δ) (hΔ : Δ≤1/1000) (hεm : 0<εm)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκβ : 2*HeckeZeroSupremum.beta-1≤3/4+2*Δ) :
    ∃meshmax : ℝ,0< meshmax ∧ ∃J : ℕ,∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(rows : Finset FreeRow)(slots : Finset Slot)(w σ v : Slot→ℝ)
        (t : FreeRow→ℝ)(θ : Slot→RayQuotient.Characters M H),
      (∀s∈slots,0<w s) → (∀s∈slots,lo≤σ s) → (∀s∈slots,σ s≤hi) →
      (∀u∈rows,((Ideal.span {u.val}).absNorm:ℝ)≤Z^d) →
      (∀u∈rows,‖ConcreteTraceCRT.eisEmbedding u.val‖^2≤Z^d) →
      (∀u∈rows,∀j,initialKeep (cleanWholeBase M H hH η η₀ j)
        (internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) u.val) →
      (∀s∈slots,∀j,
        ((DetectorDictionaryInverseRawInitialGates.deletedBase
          (momentData (cleanWholeBase M H hH η η₀ j))).modulus.absNorm:ℝ)<(Z^d)^(w s)) →
      ∀(χ : FreeRow→Character)(holes : FreeRow→Ideal O),
      (∀u∈rows,holes u≠0) →
      (∀u∈rows,∀K,idealCoeff (χ u) K=
        idealCoeff (excluded (naturalRow η u.val u.property.1).character (holes u)) K) →
      ∀a mesh height : ℝ,∀i : ℕ,i≤I →
      17/25≤2*a-1 → 2*a-1≤7/10 →
      0≤ mesh → mesh≤ meshmax → binWidth≤(2*a-1)/2 →
      (∀s∈slots,w s≤ mesh) →
      0≤height → 2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i:ℕ)*Z^τ≤height →
      (∀s∈slots,|v s|≤height) → (∀u∈rows,|t u|≤height) →
      ∀hχ : ∀u∈rows,∀j,(wholeSourceFamily M H hH η₀ (χ u) j).residue≠1,
      (∀u : rows,zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u : rows,a≤zeroMaximum (wholeSourceFamily M H hH η₀ (χ u.val)) (hχ u.val u.property)
        ((3*i:ℕ)*Z^τ)) →
      (∀u∈rows,∀j,(wholeCleanFamily M H hH η η₀ u j).modulus.absNorm≤Z^d) →
      (∀u∈rows,∀s∈slots,‖wholeCleanSlot M H hH η η₀ W (Z^d) w σ v t θ u s‖
        ≤((Z^d)^(w s))^((2*a-1)/2+binWidth)) →
      (∑u∈rows,(∏s∈slots,max 1 ‖wholeCleanSlot M H hH η η₀ W (Z^d) w σ v t θ u s‖)^2)≤
        C*(1+height)^J*
        (Z^d)^(VariableSupply.density (2*a-1)+(2*a-1)*(∑s∈slots,w s)-
          (7/45)*VariableSupply.chosenWidth (∑s∈slots,w s)+
          156*ε+mesh+εm+2*binWidth*(∑s∈slots,w s)+ηloss) := by
  obtain ⟨meshmax,hm,J,C,hC,hcount⟩ :=
    Cycle62ActualWeighted.actual_max_weighted_from_buffered_maxima (Slot:=Slot) M H hH
      (cleanWholeBase M H hH η η₀) (wholeSourceAnchor M H hH η₀) bad
      hbadM hbad0 hbadTop hbad72 setup W lo hi bΦ Δ εm binWidth ηloss
      dmin dmax τ ε e κw ηw I hdmin hdmax hτ hτzero hτheight hε hεsmall he he'
      hκw hκw' hηw hbudget hWs hW hbΦ hrad hbin hη hΔ0 hΔ hεm hβ hκβ
  refine ⟨meshmax,hm,J,C,hC,?_⟩
  filter_upwards [hcount] with Z hcount
  refine ⟨hcount.1,?_⟩
  intro d hd hd' rows slots w σ v t θ hw hlo hhi hrow hnorm hkeep hlarge
    χ holes hholes hcoeff a mesh height i hiI ha0 ha hmesh hmeshmax hbin' hwm hh hf hv ht
    hχ hnext hcurrent hmod hQ
  let B := wholeNaturalBatch M H hH η η₀ bad W lo hi (Z^d) hWs rows slots w σ v t θ
    hw hlo hhi hrow hnorm hkeep hlarge
  have he (u : FreeRow) (hu : u∈rows) :=
    whole_family_clean_maximum M H hH η η₀ (χ u) u.val u.property.1 (holes u)
      (hholes u hu) (hcoeff u hu) (hχ u hu)
  let hc : ∀u∈B.rows,∀j,(B.family u j).residue≠1 := fun u hu=>(he u hu).choose
  have hmax (u : FreeRow) (hu : u∈rows) (T : ℝ) :
      zeroMaximum (B.family u) (hc u hu) T=
      zeroMaximum (wholeSourceFamily M H hH η₀ (χ u)) (hχ u hu) T :=
    (he u hu).choose_spec T
  exact hcount.2 d hd hd' B a mesh height i hiI ha0 ha hmesh hmeshmax hbin' hwm hh hf hv ht hc
    (fun u=>by rw [hmax u.val u.property];exact hnext u)
    (fun u=>by rw [hmax u.val u.property];exact hcurrent u) hmod hQ

end
end OAI.SevenEighths.Cycle62MarkedPlain
#print axioms OAI.SevenEighths.Cycle62MarkedPlain.actual_whole_max_weighted
