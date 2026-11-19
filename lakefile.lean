import Lake
open Lake DSL

package «YM-By-Perelmans-surgery-method» where
  -- Settings applied to both it and its dependencies
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

@[default_target]
lean_lib «YMSurgery» where
  srcDir := "src"
  globs := #[.submodules `Physlib, .submodules `PhyslibAlpha, .submodules `NavaRobertsonIndependent,
    .one `AdjDegree, .one `AreaBound, .one `AreaLawBound, .one `AxialArea, .one `AxialBox, .one `AxialLoop, .one `AxialSeeds, .one `AxialSlab, .one `ClusterBound, .one `CoherenceDefect, .one `ConfinementBridge, .one `CubeAreaLaw, .one `CubeSpectrumBridge, .one `FibreBand, .one `FibreSurgery, .one `GravitationalBridge, .one `HamiltonianBridge, .one `KogutSusskindBridge, .one `KoteckyPreiss, .one `LatticeFiberDirac, .one `PerronOverlap, .one `PolymerBound, .one `PolymerDecomposition, .one `«SU2-SU3», .one `SUNBridge, .one `SlabChain, .one `SlabFin, .one `SlabInsert, .one `SlabLimit, .one `SpectralGap, .one `SurgeryGapClosure, .one `TotalUnifiedGap, .one `FormalizationPhysicsTotalUnifiedGap, .one `TransferBridge, .one `TreeBound, .one `Z2AreaLaw, .one `Z2Final, .one `Z2Gap, .one `Z2Hj, .one `Z2Spectral, .one `Z2Transfer, .one `Z2Wilson, .one `Z2WilsonGap, .one `Cube.AlgState, .one `Cube.AxisCommutation, .one `Cube.Basic, .one `Cube.DefectBand, .one `Cube.MandelstamTamm, .one `Cube.Spectrum, .one `Cube.VolumetricQuantum]
  roots := #[
    `AdjDegree,
    `AreaBound,
    `AreaLawBound,
    `AxialArea,
    `AxialBox,
    `AxialLoop,
    `AxialSeeds,
    `AxialSlab,
    `ClusterBound,
    `CoherenceDefect,
    `ConfinementBridge,
    `CubeAreaLaw,
    `CubeSpectrumBridge,
    `FibreBand,
    `FibreSurgery,
    `GravitationalBridge,
    `HamiltonianBridge,
    `KogutSusskindBridge,
    `KoteckyPreiss,
    `LatticeFiberDirac,
    `PerronOverlap,
    `PolymerBound,
    `PolymerDecomposition,
    `«SU2-SU3»,
    `SUNBridge,
    `SlabChain,
    `SlabFin,
    `SlabInsert,
    `SlabLimit,
    `SpectralGap,
    `SurgeryGapClosure,
    `TotalUnifiedGap,
    `FormalizationPhysicsTotalUnifiedGap,
    `TransferBridge,
    `TreeBound,
    `Z2AreaLaw,
    `Z2Final,
    `Z2Gap,
    `Z2Hj,
    `Z2Spectral,
    `Z2Transfer,
    `Z2Wilson,
    `Z2WilsonGap,
    `Cube.AlgState,
    `Cube.AxisCommutation,
    `Cube.Basic,
    `Cube.DefectBand,
    `Cube.MandelstamTamm,
    `Cube.Spectrum,
    `Cube.VolumetricQuantum
  ]
