import Lake
open Lake DSL

package «YM-By-Perelmans-surgery-method» where
  -- Settings applied to both it and its dependencies
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «YMSurgery» where
  srcDir := "src"
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
    `HamiltonianBridge,
    `KoteckyPreiss,
    `LatticeFiberDirac,
    `PerronOverlap,
    `PolymerBound,
    `PolymerDecomposition,
    «SU2-SU3»,
    `SUNBridge,
    `SlabChain,
    `SlabFin,
    `SlabInsert,
    `SlabLimit,
    `SpectralGap,
    `SurgeryGapClosure,
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
