-- Type.hs ---
--
-- Filename: Type.hs
-- Description:
-- Author: Manuel Schneckenreither
-- Maintainer:
-- Created: Fri Sep  5 09:06:31 2014 (+0200)
-- Version:
-- Package-Requires: ()
-- Last-Updated: Sat Apr  8 15:22:37 2017 (+0200)
--           By: Manuel Schneckenreither
--     Update #: 15
-- URL:
-- Doc URL:
-- Keywords:
-- Compatibility:
--
--

-- Commentary:
--
--
--
--

-- Change Log:
--
--
--
--
-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the GNU General Public License as
-- published by the Free Software Foundation; either version 3, or
-- (at your option) any later version.
--
-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
-- General Public License for more details.
--
-- You should have received a copy of the GNU General Public License
-- along with this program; see the file COPYING.  If not, write to
-- the Free Software Foundation, Inc., 51 Franklin Street, Fifth
-- Floor, Boston, MA 02110-1301, USA.
--
--

-- Code:

-- | TODO: comment this module
module Tct.Trs.Processor.ARA.ByInferenceRules.Operator.Type
    ( Comparison (..)
    )
    where

data Comparison = Eq | Geq -- | Leq | Times | Plus | Minus | Exp
                deriving (Eq)

instance Show Comparison where
    show Eq  = "="
    show Geq = ">="
    -- show Gt    = ">"
    -- show Lt    = "<"
    -- show Leq   = "<="
    -- show Times = "*"
    -- show Plus  = "+"
    -- show Minus = "-"
    -- show Exp   = "^"


--
-- Type.hs ends here
