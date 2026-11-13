import Lake
open Lake DSL

package proofmap

require Stacks from git
  "https://github.com/AxiomMath/Stacks.git" @ "c496df0d9beea9deaeabcea8492605f9a0a2313b"

@[default_target]
lean_lib Proof where
  roots := #[
    `GRR.ToddSeries,
    `GRR.GradedExp,
    `GRR.GradedHom,
    `GRR.ToddClass,
    `GRR.Pullback,
    `GRR.PushforwardK,
    `GRR.Statement,
    `GRR.Projection,
    `GRR.ClosedImmersion,
    `GRR.Main,
    `GRR.HRR,
    `GRR.ProjectionK,
    `GRR.ProjectionGen,
    `GRR.ProjectionTau,
    `GRR.Koszul,
    `GRR.Final,
    `GRR.PerfectCh,
    `GRR.DeformationGeom,
    `GRR.Specialization,
    `GRR.ClosedFormulaCore,
    `GRR.ZeroSectionRR,
    `GRR.ClosedImmersionReduce,
    `GRR.Theorem
  ]
