import Euler.PacketPrimaryRegularity
import Euler.PacketPrimaryParity
import Euler.PacketTerminalEnvelope
import Euler.TransversePacketJets
import Euler.TransversePacketInitialRepresentative

/-!
The actual compact-wave primary starting at time zero.  It is the genuine
homogeneous forward evolution, has the prescribed initial field, and supplies
the literal homogeneous equation and all primary regularity/parity inputs.
-/

noncomputable section

namespace EulerPacketForwardPrimary

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerPacketPointJets
  EulerPacketCylinderField EulerPacketProfileRecursion EulerTransversePacketProvider
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderFieldReflection
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (Y : InitialData P D)

abbrev forcing : Forcing P D (0 : VectorField) := homogeneousForcing D
abbrev vector : VectorField := (forcing D).vector Y
abbrev scalar : ScalarField := (forcing D).scalar Y
abbrev derivative : VectorField := (forcing D).vectorDerivative Y

omit [CompleteSpace U] in
theorem forcing_path_zero : (forcing (P := P) D).path = 0 := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  rfl

def profile (O : Operators) : Profile := homogeneousPrimary D Y O

def regularity (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector P) :
    ProfileRegularity P D.T D.T_pos.le D.support (profile D Y O) :=
  homogeneousPrimaryRegularity D Y O hcorrector

theorem equation (t : Icc (0 : ℝ) D.T) (x : Space) (θ : ℝ) :
    linearPart (D.strain (t,(x,θ))) (slicedJet (Icc (0 : ℝ) D.T) (vector D Y) (t,(x,θ)))+
      fastPressure (D.normalField (t,(x,θ))) (pressureJet (scalar D Y) (t,(x,θ))) = 0 :=
  (forcing D).jet_equation Y t x θ

theorem tangent (t : ℝ) (x : Space) (θ : ℝ) :
    inner ℝ (D.normalField (t,(x,θ))) (vector D Y (t,(x,θ))) = 0 :=
  (forcing D).vector_tangent Y t x θ

theorem mean_zero (t : ℝ) (x : Space) :
    (∫ θ in (0 : ℝ)..P, vector D Y (t,(x,θ))) = 0 :=
  (forcing D).vector_mean_zero Y t x

theorem pressure_smooth (t : ℝ) : ContDiff ℝ ∞ (fun y : Space × ℝ => scalar D Y (t,y)) :=
  (forcing D).scalar_spatial_smooth Y t

theorem parity (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector P)
    (hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)
    (hF : ∀ t x, D.F.field t (-x) = D.F.field t x)
    (hM : ∀ t x, D.M.field t (-x) = D.M.field t x)
    (hY : reflection P (Y.value : CylinderL2 P U) = -(Y.value : CylinderL2 P U)) :
    ProfileParity D.T (profile D Y O) :=
  homogeneousPrimaryParity D Y O hcorrector hSym hF hM hY

end EulerPacketForwardPrimary

namespace EulerPacketTerminalDatum

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerPacketPointJets
  EulerPacketCylinderField EulerPacketProfileRecursion EulerTransversePacketProvider
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderFieldReflection
  EulerSpatialCutoffs EulerPeriodicProfile EulerCylinderSmoothOrbit EulerMetricTransport
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  (D : Data U) (δ : ℝ) (hδ : 0 < δ) (ξ : U)
  (hs : tsupport innerCutoff ⊆ D.support)

def forwardPrimary (O : Operators) : Profile :=
  EulerPacketForwardPrimary.profile D (initialData D δ hδ ξ hs) O

def forwardPrimaryRegularity (O : Operators) (hcorrector : O.curlCorrector = D.curlCorrector period) :
    ProfileRegularity period D.T D.T_pos.le D.support (forwardPrimary D δ hδ ξ hs O) :=
  EulerPacketForwardPrimary.regularity D (initialData D δ hδ ξ hs) O hcorrector








end EulerPacketTerminalDatum
