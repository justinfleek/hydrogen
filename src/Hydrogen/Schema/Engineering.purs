-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // engineering
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Engineering pillar — Complete CAD/Blueprint drawing primitives.
-- |
-- | ## Overview
-- |
-- | The Engineering pillar provides all primitives needed to create
-- | technical drawings, blueprints, and CAD documentation:
-- |
-- | - **Tolerance**: GD&T symbols, tolerances, datum references
-- | - **Dimension**: Dimension lines, arrowheads, text formatting
-- | - **Section**: Cut planes, hatching patterns, section views
-- | - **Drawing**: Sheet sizes, title blocks, scales, views
-- |
-- | ## Why Engineering Matters
-- |
-- | At billion-agent scale, engineering primitives enable:
-- |
-- | - **Manufacturing**: Direct machine-readable specifications
-- | - **Inspection**: Automated quality control criteria
-- | - **Documentation**: Standardized technical drawings
-- | - **Collaboration**: Interoperable CAD data exchange
-- |
-- | ## Standards Supported
-- |
-- | - **ASME Y14.5-2018**: GD&T (US standard)
-- | - **ISO 1101:2017**: Geometric tolerancing (international)
-- | - **ISO 128/129**: Technical drawings
-- | - **ISO 5457/7200**: Sheet sizes and title blocks
-- |
-- | ## Submodules
-- |
-- | - `Engineering.Tolerance`: GD&T, tolerances, surface finish
-- | - `Engineering.Dimension`: Dimension lines and values
-- | - `Engineering.Section`: Section views and hatching
-- | - `Engineering.Drawing`: Sheets, title blocks, scales
-- |
-- | ## Related Modules
-- |
-- | - `Geometry.*`: Basic shapes, paths, transforms
-- | - `Dimension.Physical`: Physical length units
-- | - `Physical.Mechanical`: Material properties
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Engineering as Eng
-- | import Hydrogen.Schema.Engineering.Tolerance as Tol
-- | import Hydrogen.Schema.Engineering.Dimension as Dim
-- |
-- | -- Create a positional tolerance with datum references
-- | positionTol = Tol.frameWithDatums
-- |   Tol.Position
-- |   (Tol.toleranceValue 0.1)
-- |   (Tol.primaryDatum Tol.DatumA)
-- |   (Just (Tol.secondaryDatum Tol.DatumB))
-- |   Nothing
-- |
-- | -- Create a dimension
-- | linearDim = Dim.horizontalDimension 0.0 0.0 100.0 0.0 10.0
-- |   (Dim.dimensionText (Dim.linearDimension 100.0))
-- | ```

module Hydrogen.Schema.Engineering
  ( -- * Re-exports
    module Hydrogen.Schema.Engineering.Tolerance
  , module Hydrogen.Schema.Engineering.Dimension
  , module Hydrogen.Schema.Engineering.Section
  , module Hydrogen.Schema.Engineering.Drawing
  ) where

import Hydrogen.Schema.Engineering.Tolerance
  ( -- Geometric Characteristics
    GeometricCharacteristic(Straightness, Flatness, Circularity, Cylindricity, Perpendicularity, Angularity, Parallelism, Position, Concentricity, Symmetry, CircularRunout, TotalRunout, ProfileOfLine, ProfileOfSurface)
  , allGeometricCharacteristics
  , characteristicSymbol
  , characteristicCategory
  , characteristicDescription
  -- Tolerance Categories
  , ToleranceCategory(Form, Orientation, Location, Runout, Profile)
  , allToleranceCategories
  -- Tolerance Value
  , ToleranceValue
  , toleranceValue
  , toleranceValueUnsafe
  , unwrapTolerance
  , toleranceBounds
  , toleranceMm
  , toleranceTight
  , tolerancePrecision
  , toleranceStandard
  , toleranceLoose
  -- Datum Reference
  , DatumLabel(DatumA, DatumB, DatumC, DatumD, DatumE, DatumF, DatumG, DatumH, DatumJ, DatumK, DatumL, DatumM, DatumN, DatumP, DatumR, DatumS, DatumT, DatumU, DatumV, DatumW, DatumX, DatumY, DatumZ)
  , allDatumLabels
  , datumLabelChar
  , DatumFeature(DatumFeature)
  , datumFeature
  , primaryDatum
  , secondaryDatum
  , tertiaryDatum
  -- Material Condition
  , MaterialCondition(MMC, LMC, RFS)
  , allMaterialConditions
  , conditionSymbol
  , conditionDescription
  -- Feature Control Frame
  , FeatureControlFrame(FeatureControlFrame)
  , featureControlFrame
  , simpleFrame
  , frameWithDatums
  , frameWithModifier
  -- Tolerances
  , BilateralTolerance(BilateralTolerance)
  , symmetricTolerance
  , asymmetricTolerance
  , plusTolerance
  , minusTolerance
  , UnilateralTolerance(UnilateralPlus, UnilateralMinus)
  , unilateralPlus
  , unilateralMinus
  , LimitDimension(LimitDimension)
  , limitDimension
  , limitFromBilateral
  -- Fit Classes
  , FitClass(H11c11, H9d9, H8f7, H7g6, H7h6, H7k6, H7m6, H7n6, H7p6, H7s6, H7u6)
  , allFitClasses
  , fitDescription
  , fitTolerance
  -- Surface Finish
  , SurfaceFinish
  , surfaceFinish
  , surfaceFinishUnsafe
  , unwrapFinish
  , finishBounds
  , roughnessRa
  , finishMirror
  , finishGround
  , finishMachined
  , finishRough
  , finishCast
  -- Operations
  , isFormTolerance
  , isOrientationTolerance
  , isLocationTolerance
  , isRunoutTolerance
  , requiresDatum
  , toleranceStackUp
  )

import Hydrogen.Schema.Engineering.Dimension
  ( -- Dimension Type
    DimensionType(Linear, Angular, Radial, Diameter, ArcLength, Ordinate, Chain, Baseline)
  , allDimensionTypes
  , dimensionTypeDescription
  -- Arrowhead Style
  , ArrowheadStyle(FilledArrow, OpenArrow, ClosedArrow, Tick, Dot, OpenDot, ArchitecturalTick, Integral, NoArrow)
  , allArrowheadStyles
  , arrowheadDescription
  -- Dimension Value
  , DimensionValue(LinearValue, AngularValue, RadialValue, DiameterValue, ArcLengthValue)
  , linearDimension
  , angularDimension
  , radialDimension
  , diameterDimension
  , arcLengthDimension
  -- Dimension Text
  , DimensionText(BasicDimensionText, LimitDimensionText, ReferenceDimensionText, BasicBoxedText)
  , dimensionText
  , textWithTolerance
  , textWithLimits
  , referenceText
  , basicText
  -- Text Position
  , TextPosition(TextAbove, TextCentered, TextBelow, TextInline, TextOutside)
  , allTextPositions
  -- Linear Dimension
  , LinearDimension(LinearDimension)
  , horizontalDimension
  , verticalDimension
  , alignedDimension
  , rotatedDimension
  -- Angular Dimension
  , AngularDimension(AngularDimension)
  , angularDim
  , arcAngleDimension
  -- Radial Dimension
  , RadialDimension(RadiusDim, DiameterDim, CenterMarkDim, CenterLineDim)
  , radiusDimension
  , diameter
  , centerMark
  , centerLine
  -- Ordinate Dimension
  , OrdinateDimension(OrdinateDimension)
  , xOrdinate
  , yOrdinate
  -- Chain Dimension
  , ChainDimension(ChainDim, BaselineDim)
  , chainDimension
  , baselineDimension
  -- Dimension Style
  , DimensionStyle(DimensionStyle)
  , defaultStyle
  , isoStyle
  , asmeStyle
  -- Operations
  , formatValue
  , totalChainLength
  )

import Hydrogen.Schema.Engineering.Section
  ( -- Section Type
    SectionType(FullSection, HalfSection, OffsetSection, BrokenOutSection, RevolvedSection, RemovedSection, AlignedSection)
  , allSectionTypes
  , sectionTypeDescription
  -- Cut Plane
  , CutPlane(SimplePlane, OffsetPlane, BentPlane)
  , cutPlane
  , offsetCutPlane
  , bentCutPlane
  -- Section Line
  , SectionLine(SectionLine)
  , sectionLine
  , sectionLineWithArrows
  -- Hatch Pattern
  , HatchPattern(SolidFill, GeneralPurpose, Steel, CastIron, Bronze, Brass, Aluminum, Rubber, Plastic, Glass, Concrete, Brick, Stone, Wood, Earth, Water, Insulation, CustomPattern)
  , allHatchPatterns
  , patternDescription
  , patternForMaterial
  -- Hatch Style
  , HatchStyle(HatchStyle)
  , hatchStyle
  , defaultHatch
  , steelHatch
  , brassHatch
  , castIronHatch
  -- Hatched Region
  , HatchedRegion(HatchedRegion)
  , hatchedRegion
  , hatchWithBoundary
  -- Section View
  , SectionView(SectionView)
  , fullSection
  , halfSection
  , offsetSection
  , brokenOutSection
  -- Operations
  , rotateHatch
  , scaleHatch
  )

import Hydrogen.Schema.Engineering.Drawing
  ( -- Sheet Size
    SheetSize(A0, A1, A2, A3, A4, ANSI_A, ANSI_B, ANSI_C, ANSI_D, ANSI_E, Arch_A, Arch_B, Arch_C, Arch_D, Arch_E, CustomSize)
  , allSheetSizes
  , sheetDimensions
  , sheetDescription
  -- Sheet Orientation
  , SheetOrientation(Portrait, Landscape)
  , allSheetOrientations
  -- Drawing Scale
  , DrawingScale(DrawingScale)
  , scaleRatio
  , fullScale
  , halfScale
  , doubleScale
  , customScale
  , scaleToText
  , scale1to1
  , scale1to2
  , scale1to5
  , scale1to10
  , scale1to20
  , scale1to50
  , scale1to100
  , scale2to1
  , scale5to1
  , scale10to1
  -- Title Block
  , TitleBlock(TitleBlock)
  , titleBlock
  , minimalTitleBlock
  -- Revision
  , Revision(Revision)
  , revision
  , initialRevision
  -- Bill of Materials
  , BomEntry(BomEntry)
  , bomEntry
  , BillOfMaterials(BillOfMaterials)
  , billOfMaterials
  , addBomEntry
  , bomTotal
  -- View Type
  , ViewType(FrontView, RearView, TopView, BottomView, LeftView, RightView, IsometricView_, DiametricView, TrimetricView, DetailView_, AuxiliaryView, SectionView_)
  , allViewTypes
  , viewTypeDescription
  -- Drawing View
  , DrawingView(DrawingView)
  , orthographicView
  , isometricView
  , detailView
  -- Drawing Sheet
  , DrawingSheet(DrawingSheet)
  , drawingSheet
  , addView
  -- Operations
  , actualToDrawing
  , drawingToActual
  )
