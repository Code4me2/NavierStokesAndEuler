import Euler.OrdinaryEulerSobolevClass

/-! The reverse bridge from ordinary scalar-pressure Euler to the
projected equation. The only regularity inputs are the velocity and its
actual strong time derivative in all spatial Sobolev orders. Neither a
pressure-force regularity hypothesis nor a projected equation is assumed.
The scalar pressure may be changed by an arbitrary function of time. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerMeanClassical
  EulerMeanOrdinaryLift EulerMeanSmoothRepresentative EulerSmoothFieldSobolevTime
  EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerVolterraConvolution
open scoped ContDiff

private local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

variable {T : ℝ} {hT : 0 ≤ T}

/-- The force obtained from the actual velocity and its actual time derivative. -/
def scalarEulerForce (A B : SmoothL2Field Space) : SmoothL2Field Space :=
  fieldNeg (addField B (advectionField A A))

theorem scalarEulerForce_field (A B : SmoothL2Field Space) (x : Space) :
    (scalarEulerForce A B).field x = -((B.field x)+fderiv ℝ A.field x (A.field x)) := by
  simp only [scalarEulerForce,fieldNeg_field,addField_field,advectionField_field]


/-- An ordinary scalar Euler equation implies the actual projected L² equation.
Spatial differentiability of pressure is used only at interior times. -/
theorem isSmoothProjectedEuler_of_scalarEuler
    (A B : Icc (0 : ℝ) T → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
    (hd : ∀ t (ht : t ∈ Ioo 0 T),
      HasDerivAt (fun r => (A (projIcc 0 T hT r)).toLp)
        (B ⟨t,ht.1.le,ht.2.le⟩).toLp t)
    (p : ℝ → Space → ℝ)
    (hdiv : ∀ t x, divergence (A t).field x=0)
    (hp : ∀ t ∈ Ioo 0 T, Differentiable ℝ (p t))
    (he : ∀ t (ht : t ∈ Ioo 0 T) x,
      (B ⟨t,ht.1.le,ht.2.le⟩).field x+
        fderiv ℝ (A ⟨t,ht.1.le,ht.2.le⟩).field x
          ((A ⟨t,ht.1.le,ht.2.le⟩).field x)+gradient (p t) x=0) :
    IsSmoothProjectedEuler (hT := hT) A := by
  have hs (t : Icc (0 : ℝ) T) : (A t).toLp ∈ solenoidalSpace :=
    smooth_mem_solenoidal (A t).field (A t).smooth (A t).memLp (hdiv t)
  refine ⟨hA,hs,?_⟩
  intro t ht
  let s : Icc (0 : ℝ) T := ⟨t,ht.1.le,ht.2.le⟩
  let G := scalarEulerForce (A s) (B s)
  have hg (x : Space) : G.field x=gradient (p t) x := by
    rw [scalarEulerForce_field]
    exact (eq_neg_of_add_eq_zero_right (he t ht x)).symm
  have hG : G.toLp ∈ EulerMeanSolenoidal.gradientSpace :=
    gradient_mem G (p t) (potential_smooth G (p t) (hp t ht) hg) hg
  have hproj := solenoidalProjection.hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have hfix : (fun r => solenoidalProjection (A (projIcc 0 T hT r)).toLp)=
      (fun r => (A (projIcc 0 T hT r)).toLp) := by
    funext r
    exact solenoidalSpace.starProjection_eq_self_iff.mpr (hs _)
  simp only [Function.comp_def] at hproj
  rw [hfix] at hproj
  have hB : solenoidalProjection (B s).toLp=(B s).toLp := hproj.unique (hd t ht)
  have hzero := (solenoidalProjection_eq_zero_iff G.toLp).mpr hG
  change solenoidalProjection (fieldNeg (addField (B s) (advectionField (A s) (A s)))).toLp=0 at hzero
  rw [toLp_fieldNeg,toLp_addField,map_neg,map_add,hB] at hzero
  have hR : (B s).toLp=(projectedRhs (A s)).toLp := by
    rw [projectedRhs_toLp]
    exact eq_neg_of_add_eq_zero_left (neg_eq_zero.mp hzero)
  exact hR ▸ hd t ht


section Identification

variable (A B : Icc (0 : ℝ) T → SmoothL2Field Space)
  (hA : ∀ n, Continuous (fun t => (A t).jetLp n))
  (hB : ∀ n, Continuous (fun t => (B t).jetLp n))
  (hd : ∀ t (ht : t ∈ Ioo 0 T),
    HasDerivAt (fun r => (A (projIcc 0 T hT r)).toLp)
      (B ⟨t,ht.1.le,ht.2.le⟩).toLp t)
  (p : ℝ → Space → ℝ)
  (hdiv : ∀ t x, divergence (A t).field x=0)
  (hp : ∀ t ∈ Ioo 0 T, Differentiable ℝ (p t))
  (he : ∀ t (ht : t ∈ Ioo 0 T) x,
    (B ⟨t,ht.1.le,ht.2.le⟩).field x+
      fderiv ℝ (A ⟨t,ht.1.le,ht.2.le⟩).field x
        ((A ⟨t,ht.1.le,ht.2.le⟩).field x)+gradient (p t) x=0)





end Identification


/-- The scalar-pressure form of the smooth ordinary Euler class. The
all-order spatial paths represent `C H^m` for every finite `m`. A single
strong L² time law and the continuous all-order derivative paths imply
the strong time law in every Sobolev order by `sobolev_derivative_of_l2`.
No norm, time regularity, or normalization is imposed on the scalar pressure. -/
def IsSmoothScalarEuler (A : Icc (0 : ℝ) T → SmoothL2Field Space) : Prop :=
  (∀ n, Continuous (fun t => (A t).jetLp n)) ∧
    ∃ (B : Icc (0 : ℝ) T → SmoothL2Field Space) (p : ℝ → Space → ℝ),
      (∀ n, Continuous (fun t => (B t).jetLp n)) ∧
      (∀ t (ht : t ∈ Ioo 0 T),
        HasDerivAt (fun r => (A (projIcc 0 T hT r)).toLp)
          (B ⟨t,ht.1.le,ht.2.le⟩).toLp t) ∧
      (∀ t x, divergence (A t).field x=0) ∧
      (∀ t ∈ Ioo 0 T, Differentiable ℝ (p t)) ∧
      (∀ t (ht : t ∈ Ioo 0 T) x,
        (B ⟨t,ht.1.le,ht.2.le⟩).field x+
          fderiv ℝ (A ⟨t,ht.1.le,ht.2.le⟩).field x
            ((A ⟨t,ht.1.le,ht.2.le⟩).field x)+gradient (p t) x=0)



theorem scalarEuler_iff_projected (A : Icc (0 : ℝ) T → SmoothL2Field Space) :
    IsSmoothScalarEuler (hT := hT) A ↔ IsSmoothProjectedEuler (hT := hT) A := by
  constructor
  · rintro ⟨hA,B,p,_hB,hd,hdiv,hp,he⟩
    exact isSmoothProjectedEuler_of_scalarEuler A B hA hd p hdiv hp he
  · intro hA
    let U := evolutionOfProjectedEquation A hA
    refine ⟨hA.1,U.derivative,(fun r => U.scalarPressure (projIcc 0 T hT r)),
      U.derivative_continuous,?_,?_,?_,?_⟩
    · intro t ht
      have h := U.velocityPath_hasDerivWithinAt ⟨t,ht.1.le,ht.2.le⟩
      rw [U.velocityPath_extend] at h
      exact h.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    · intro t x
      exact solenoidal_representative_divergence _ (hA.2.1 t) _ (A t).smooth (A t).toLp_ae x
    · intro t ht
      exact (U.scalarPressure_spec (projIcc 0 T hT t)).1.differentiable (by simp)
    · intro t ht x
      dsimp only
      rw [projIcc_of_mem hT ⟨ht.1.le,ht.2.le⟩,
        (U.scalarPressure_spec ⟨t,ht.1.le,ht.2.le⟩).2.2 x,U.derivative_field]
      change (-fderiv ℝ (A ⟨t,ht.1.le,ht.2.le⟩).field x
        ((A ⟨t,ht.1.le,ht.2.le⟩).field x)-
        (U.pressureForce ⟨t,ht.1.le,ht.2.le⟩).field x)+_+_=0
      abel

theorem exists_evolution_iff_scalar (hpos : 0 < T)
    (A : Icc (0 : ℝ) T → SmoothL2Field Space) :
    (∃ U : Evolution T hT, U.velocity=A) ↔ IsSmoothScalarEuler (hT := hT) A :=
  (exists_evolution_iff_projected hpos A).trans (scalarEuler_iff_projected A).symm

end EulerOrdinarySobolev
