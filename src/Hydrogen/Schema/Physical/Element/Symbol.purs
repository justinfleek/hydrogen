-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // physical // element // symbol
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element Symbols and Names.
-- |
-- | ## PURPOSE
-- | IUPAC-standard element symbols (1-2 characters) and full names.
-- | Used for display, serialization, and lookup.
-- |
-- | ## AUTHORITY
-- | IUPAC - all symbols and names per 2024 periodic table.

module Hydrogen.Schema.Physical.Element.Symbol
  ( symbol
  , name
  , fromSymbol
  ) where

import Prelude
  ( (==)
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (toUpper)
import Hydrogen.Schema.Physical.Element (Element(Hydrogen, Helium, Lithium, Beryllium, Boron, Carbon, Nitrogen, Oxygen, Fluorine, Neon, Sodium, Magnesium, Aluminium, Silicon, Phosphorus, Sulfur, Chlorine, Argon, Potassium, Calcium, Scandium, Titanium, Vanadium, Chromium, Manganese, Iron, Cobalt, Nickel, Copper, Zinc, Gallium, Germanium, Arsenic, Selenium, Bromine, Krypton, Rubidium, Strontium, Yttrium, Zirconium, Niobium, Molybdenum, Technetium, Ruthenium, Rhodium, Palladium, Silver, Cadmium, Indium, Tin, Antimony, Tellurium, Iodine, Xenon, Cesium, Barium, Lanthanum, Cerium, Praseodymium, Neodymium, Promethium, Samarium, Europium, Gadolinium, Terbium, Dysprosium, Holmium, Erbium, Thulium, Ytterbium, Lutetium, Hafnium, Tantalum, Tungsten, Rhenium, Osmium, Iridium, Platinum, Gold, Mercury, Thallium, Lead, Bismuth, Polonium, Astatine, Radon, Francium, Radium, Actinium, Thorium, Protactinium, Uranium, Neptunium, Plutonium, Americium, Curium, Berkelium, Californium, Einsteinium, Fermium, Mendelevium, Nobelium, Lawrencium, Rutherfordium, Dubnium, Seaborgium, Bohrium, Hassium, Meitnerium, Darmstadtium, Roentgenium, Copernicium, Nihonium, Flerovium, Moscovium, Livermorium, Tennessine, Oganesson))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // symbol
-- ═════════════════════════════════════════════════════════════════════════════

-- | IUPAC element symbol (1-2 characters).
symbol :: Element -> String
symbol Hydrogen = "H"
symbol Helium = "He"
symbol Lithium = "Li"
symbol Beryllium = "Be"
symbol Boron = "B"
symbol Carbon = "C"
symbol Nitrogen = "N"
symbol Oxygen = "O"
symbol Fluorine = "F"
symbol Neon = "Ne"
symbol Sodium = "Na"
symbol Magnesium = "Mg"
symbol Aluminium = "Al"
symbol Silicon = "Si"
symbol Phosphorus = "P"
symbol Sulfur = "S"
symbol Chlorine = "Cl"
symbol Argon = "Ar"
symbol Potassium = "K"
symbol Calcium = "Ca"
symbol Scandium = "Sc"
symbol Titanium = "Ti"
symbol Vanadium = "V"
symbol Chromium = "Cr"
symbol Manganese = "Mn"
symbol Iron = "Fe"
symbol Cobalt = "Co"
symbol Nickel = "Ni"
symbol Copper = "Cu"
symbol Zinc = "Zn"
symbol Gallium = "Ga"
symbol Germanium = "Ge"
symbol Arsenic = "As"
symbol Selenium = "Se"
symbol Bromine = "Br"
symbol Krypton = "Kr"
symbol Rubidium = "Rb"
symbol Strontium = "Sr"
symbol Yttrium = "Y"
symbol Zirconium = "Zr"
symbol Niobium = "Nb"
symbol Molybdenum = "Mo"
symbol Technetium = "Tc"
symbol Ruthenium = "Ru"
symbol Rhodium = "Rh"
symbol Palladium = "Pd"
symbol Silver = "Ag"
symbol Cadmium = "Cd"
symbol Indium = "In"
symbol Tin = "Sn"
symbol Antimony = "Sb"
symbol Tellurium = "Te"
symbol Iodine = "I"
symbol Xenon = "Xe"
symbol Cesium = "Cs"
symbol Barium = "Ba"
symbol Lanthanum = "La"
symbol Cerium = "Ce"
symbol Praseodymium = "Pr"
symbol Neodymium = "Nd"
symbol Promethium = "Pm"
symbol Samarium = "Sm"
symbol Europium = "Eu"
symbol Gadolinium = "Gd"
symbol Terbium = "Tb"
symbol Dysprosium = "Dy"
symbol Holmium = "Ho"
symbol Erbium = "Er"
symbol Thulium = "Tm"
symbol Ytterbium = "Yb"
symbol Lutetium = "Lu"
symbol Hafnium = "Hf"
symbol Tantalum = "Ta"
symbol Tungsten = "W"
symbol Rhenium = "Re"
symbol Osmium = "Os"
symbol Iridium = "Ir"
symbol Platinum = "Pt"
symbol Gold = "Au"
symbol Mercury = "Hg"
symbol Thallium = "Tl"
symbol Lead = "Pb"
symbol Bismuth = "Bi"
symbol Polonium = "Po"
symbol Astatine = "At"
symbol Radon = "Rn"
symbol Francium = "Fr"
symbol Radium = "Ra"
symbol Actinium = "Ac"
symbol Thorium = "Th"
symbol Protactinium = "Pa"
symbol Uranium = "U"
symbol Neptunium = "Np"
symbol Plutonium = "Pu"
symbol Americium = "Am"
symbol Curium = "Cm"
symbol Berkelium = "Bk"
symbol Californium = "Cf"
symbol Einsteinium = "Es"
symbol Fermium = "Fm"
symbol Mendelevium = "Md"
symbol Nobelium = "No"
symbol Lawrencium = "Lr"
symbol Rutherfordium = "Rf"
symbol Dubnium = "Db"
symbol Seaborgium = "Sg"
symbol Bohrium = "Bh"
symbol Hassium = "Hs"
symbol Meitnerium = "Mt"
symbol Darmstadtium = "Ds"
symbol Roentgenium = "Rg"
symbol Copernicium = "Cn"
symbol Nihonium = "Nh"
symbol Flerovium = "Fl"
symbol Moscovium = "Mc"
symbol Livermorium = "Lv"
symbol Tennessine = "Ts"
symbol Oganesson = "Og"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // name
-- ═════════════════════════════════════════════════════════════════════════════

-- | IUPAC element name (English).
name :: Element -> String
name Hydrogen = "Hydrogen"
name Helium = "Helium"
name Lithium = "Lithium"
name Beryllium = "Beryllium"
name Boron = "Boron"
name Carbon = "Carbon"
name Nitrogen = "Nitrogen"
name Oxygen = "Oxygen"
name Fluorine = "Fluorine"
name Neon = "Neon"
name Sodium = "Sodium"
name Magnesium = "Magnesium"
name Aluminium = "Aluminium"
name Silicon = "Silicon"
name Phosphorus = "Phosphorus"
name Sulfur = "Sulfur"
name Chlorine = "Chlorine"
name Argon = "Argon"
name Potassium = "Potassium"
name Calcium = "Calcium"
name Scandium = "Scandium"
name Titanium = "Titanium"
name Vanadium = "Vanadium"
name Chromium = "Chromium"
name Manganese = "Manganese"
name Iron = "Iron"
name Cobalt = "Cobalt"
name Nickel = "Nickel"
name Copper = "Copper"
name Zinc = "Zinc"
name Gallium = "Gallium"
name Germanium = "Germanium"
name Arsenic = "Arsenic"
name Selenium = "Selenium"
name Bromine = "Bromine"
name Krypton = "Krypton"
name Rubidium = "Rubidium"
name Strontium = "Strontium"
name Yttrium = "Yttrium"
name Zirconium = "Zirconium"
name Niobium = "Niobium"
name Molybdenum = "Molybdenum"
name Technetium = "Technetium"
name Ruthenium = "Ruthenium"
name Rhodium = "Rhodium"
name Palladium = "Palladium"
name Silver = "Silver"
name Cadmium = "Cadmium"
name Indium = "Indium"
name Tin = "Tin"
name Antimony = "Antimony"
name Tellurium = "Tellurium"
name Iodine = "Iodine"
name Xenon = "Xenon"
name Cesium = "Cesium"
name Barium = "Barium"
name Lanthanum = "Lanthanum"
name Cerium = "Cerium"
name Praseodymium = "Praseodymium"
name Neodymium = "Neodymium"
name Promethium = "Promethium"
name Samarium = "Samarium"
name Europium = "Europium"
name Gadolinium = "Gadolinium"
name Terbium = "Terbium"
name Dysprosium = "Dysprosium"
name Holmium = "Holmium"
name Erbium = "Erbium"
name Thulium = "Thulium"
name Ytterbium = "Ytterbium"
name Lutetium = "Lutetium"
name Hafnium = "Hafnium"
name Tantalum = "Tantalum"
name Tungsten = "Tungsten"
name Rhenium = "Rhenium"
name Osmium = "Osmium"
name Iridium = "Iridium"
name Platinum = "Platinum"
name Gold = "Gold"
name Mercury = "Mercury"
name Thallium = "Thallium"
name Lead = "Lead"
name Bismuth = "Bismuth"
name Polonium = "Polonium"
name Astatine = "Astatine"
name Radon = "Radon"
name Francium = "Francium"
name Radium = "Radium"
name Actinium = "Actinium"
name Thorium = "Thorium"
name Protactinium = "Protactinium"
name Uranium = "Uranium"
name Neptunium = "Neptunium"
name Plutonium = "Plutonium"
name Americium = "Americium"
name Curium = "Curium"
name Berkelium = "Berkelium"
name Californium = "Californium"
name Einsteinium = "Einsteinium"
name Fermium = "Fermium"
name Mendelevium = "Mendelevium"
name Nobelium = "Nobelium"
name Lawrencium = "Lawrencium"
name Rutherfordium = "Rutherfordium"
name Dubnium = "Dubnium"
name Seaborgium = "Seaborgium"
name Bohrium = "Bohrium"
name Hassium = "Hassium"
name Meitnerium = "Meitnerium"
name Darmstadtium = "Darmstadtium"
name Roentgenium = "Roentgenium"
name Copernicium = "Copernicium"
name Nihonium = "Nihonium"
name Flerovium = "Flerovium"
name Moscovium = "Moscovium"
name Livermorium = "Livermorium"
name Tennessine = "Tennessine"
name Oganesson = "Oganesson"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // from symbol
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lookup element by symbol (case-insensitive).
fromSymbol :: String -> Maybe Element
fromSymbol s = go (toUpper s)
  where
  go upper
    | upper == "H" = Just Hydrogen
    | upper == "HE" = Just Helium
    | upper == "LI" = Just Lithium
    | upper == "BE" = Just Beryllium
    | upper == "B" = Just Boron
    | upper == "C" = Just Carbon
    | upper == "N" = Just Nitrogen
    | upper == "O" = Just Oxygen
    | upper == "F" = Just Fluorine
    | upper == "NE" = Just Neon
    | upper == "NA" = Just Sodium
    | upper == "MG" = Just Magnesium
    | upper == "AL" = Just Aluminium
    | upper == "SI" = Just Silicon
    | upper == "P" = Just Phosphorus
    | upper == "S" = Just Sulfur
    | upper == "CL" = Just Chlorine
    | upper == "AR" = Just Argon
    | upper == "K" = Just Potassium
    | upper == "CA" = Just Calcium
    | upper == "SC" = Just Scandium
    | upper == "TI" = Just Titanium
    | upper == "V" = Just Vanadium
    | upper == "CR" = Just Chromium
    | upper == "MN" = Just Manganese
    | upper == "FE" = Just Iron
    | upper == "CO" = Just Cobalt
    | upper == "NI" = Just Nickel
    | upper == "CU" = Just Copper
    | upper == "ZN" = Just Zinc
    | upper == "GA" = Just Gallium
    | upper == "GE" = Just Germanium
    | upper == "AS" = Just Arsenic
    | upper == "SE" = Just Selenium
    | upper == "BR" = Just Bromine
    | upper == "KR" = Just Krypton
    | upper == "RB" = Just Rubidium
    | upper == "SR" = Just Strontium
    | upper == "Y" = Just Yttrium
    | upper == "ZR" = Just Zirconium
    | upper == "NB" = Just Niobium
    | upper == "MO" = Just Molybdenum
    | upper == "TC" = Just Technetium
    | upper == "RU" = Just Ruthenium
    | upper == "RH" = Just Rhodium
    | upper == "PD" = Just Palladium
    | upper == "AG" = Just Silver
    | upper == "CD" = Just Cadmium
    | upper == "IN" = Just Indium
    | upper == "SN" = Just Tin
    | upper == "SB" = Just Antimony
    | upper == "TE" = Just Tellurium
    | upper == "I" = Just Iodine
    | upper == "XE" = Just Xenon
    | upper == "CS" = Just Cesium
    | upper == "BA" = Just Barium
    | upper == "LA" = Just Lanthanum
    | upper == "CE" = Just Cerium
    | upper == "PR" = Just Praseodymium
    | upper == "ND" = Just Neodymium
    | upper == "PM" = Just Promethium
    | upper == "SM" = Just Samarium
    | upper == "EU" = Just Europium
    | upper == "GD" = Just Gadolinium
    | upper == "TB" = Just Terbium
    | upper == "DY" = Just Dysprosium
    | upper == "HO" = Just Holmium
    | upper == "ER" = Just Erbium
    | upper == "TM" = Just Thulium
    | upper == "YB" = Just Ytterbium
    | upper == "LU" = Just Lutetium
    | upper == "HF" = Just Hafnium
    | upper == "TA" = Just Tantalum
    | upper == "W" = Just Tungsten
    | upper == "RE" = Just Rhenium
    | upper == "OS" = Just Osmium
    | upper == "IR" = Just Iridium
    | upper == "PT" = Just Platinum
    | upper == "AU" = Just Gold
    | upper == "HG" = Just Mercury
    | upper == "TL" = Just Thallium
    | upper == "PB" = Just Lead
    | upper == "BI" = Just Bismuth
    | upper == "PO" = Just Polonium
    | upper == "AT" = Just Astatine
    | upper == "RN" = Just Radon
    | upper == "FR" = Just Francium
    | upper == "RA" = Just Radium
    | upper == "AC" = Just Actinium
    | upper == "TH" = Just Thorium
    | upper == "PA" = Just Protactinium
    | upper == "U" = Just Uranium
    | upper == "NP" = Just Neptunium
    | upper == "PU" = Just Plutonium
    | upper == "AM" = Just Americium
    | upper == "CM" = Just Curium
    | upper == "BK" = Just Berkelium
    | upper == "CF" = Just Californium
    | upper == "ES" = Just Einsteinium
    | upper == "FM" = Just Fermium
    | upper == "MD" = Just Mendelevium
    | upper == "NO" = Just Nobelium
    | upper == "LR" = Just Lawrencium
    | upper == "RF" = Just Rutherfordium
    | upper == "DB" = Just Dubnium
    | upper == "SG" = Just Seaborgium
    | upper == "BH" = Just Bohrium
    | upper == "HS" = Just Hassium
    | upper == "MT" = Just Meitnerium
    | upper == "DS" = Just Darmstadtium
    | upper == "RG" = Just Roentgenium
    | upper == "CN" = Just Copernicium
    | upper == "NH" = Just Nihonium
    | upper == "FL" = Just Flerovium
    | upper == "MC" = Just Moscovium
    | upper == "LV" = Just Livermorium
    | upper == "TS" = Just Tennessine
    | upper == "OG" = Just Oganesson
    | otherwise = Nothing
