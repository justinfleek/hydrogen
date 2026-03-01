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
    GeometricCharacteristic(..)
  , allGeometricCharacteristics
  , characteristicSymbol
  , characteristicCategory
  , characteristicDescription
  -- Tolerance Categories
  , ToleranceCategory(..)
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
  , DatumLabel(..)
  , allDatumLabels
  , datumLabelChar
  , DatumFeature(..)
  , datumFeature
  , primaryDatum
  , secondaryDatum
  , tertiaryDatum
  -- Material Condition
  , MaterialCondition(..)
  , allMaterialConditions
  , conditionSymbol
  , conditionDescription
  -- Feature Control Frame
  , FeatureControlFrame(..)
  , featureControlFrame
  , simpleFrame
  , frameWithDatums
  , frameWithModifier
  -- Tolerances
  , BilateralTolerance(..)
  , symmetricTolerance
  , asymmetricTolerance
  , plusTolerance
  , minusTolerance
  , UnilateralTolerance(..)
  , unilateralPlus
  , unilateralMinus
  , LimitDimension(..)
  , limitDimension
  , limitFromBilateral
  -- Fit Classes
  , FitClass(..)
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
    DimensionType(..)
  , allDimensionTypes
  , dimensionTypeDescription
  -- Arrowhead Style
  , ArrowheadStyle(..)
  , allArrowheadStyles
  , arrowheadDescription
  -- Dimension Value
  , DimensionValue(..)
  , linearDimension
  , angularDimension
  , radialDimension
  , diameterDimension
  , arcLengthDimension
  -- Dimension Text
  , DimensionText(..)
  , dimensionText
  , textWithTolerance
  , textWithLimits
  , referenceText
  , basicText
  -- Text Position
  , TextPosition(..)
  , allTextPositions
  -- Linear Dimension
  , LinearDimension(..)
  , horizontalDimension
  , verticalDimension
  , alignedDimension
  , rotatedDimension
  -- Angular Dimension
  , AngularDimension(..)
  , angularDim
  , arcAngleDimension
  -- Radial Dimension
  , RadialDimension(..)
  , radiusDimension
  , diameter
  , centerMark
  , centerLine
  -- Ordinate Dimension
  , OrdinateDimension(..)
  , xOrdinate
  , yOrdinate
  -- Chain Dimension
  , ChainDimension(..)
  , chainDimension
  , baselineDimension
  -- Dimension Style
  , DimensionStyle(..)
  , defaultStyle
  , isoStyle
  , asmeStyle
  -- Operations
  , formatValue
  , totalChainLength
  )

import Hydrogen.Schema.Engineering.Section
  ( -- Section Type
    SectionType(..)
  , allSectionTypes
  , sectionTypeDescription
  -- Cut Plane
  , CutPlane(..)
  , cutPlane
  , offsetCutPlane
  , bentCutPlane
  -- Section Line
  , SectionLine(..)
  , sectionLine
  , sectionLineWithArrows
  -- Hatch Pattern
  , HatchPattern(..)
  , allHatchPatterns
  , patternDescription
  , patternForMaterial
  -- Hatch Style
  , HatchStyle(..)
  , hatchStyle
  , defaultHatch
  , steelHatch
  , brassHatch
  , castIronHatch
  -- Hatched Region
  , HatchedRegion(..)
  , hatchedRegion
  , hatchWithBoundary
  -- Section View
  , SectionView(..)
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
    SheetSize(..)
  , allSheetSizes
  , sheetDimensions
  , sheetDescription
  -- Sheet Orientation
  , SheetOrientation(..)
  , allSheetOrientations
  -- Drawing Scale
  , DrawingScale(..)
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
  , TitleBlock(..)
  , titleBlock
  , minimalTitleBlock
  -- Revision
  , Revision(..)
  , revision
  , initialRevision
  -- Bill of Materials
  , BomEntry(..)
  , bomEntry
  , BillOfMaterials(..)
  , billOfMaterials
  , addBomEntry
  , bomTotal
  -- View Type
  , ViewType(..)
  , allViewTypes
  , viewTypeDescription
  -- Drawing View
  , DrawingView(..)
  , orthographicView
  , isometricView
  , detailView
  -- Drawing Sheet
  , DrawingSheet(..)
  , drawingSheet
  , addView
  -- Operations
  , actualToDrawing
  , drawingToActual
  )
