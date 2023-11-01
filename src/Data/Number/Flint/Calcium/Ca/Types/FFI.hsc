module Data.Number.Flint.Calcium.Ca.Types.FFI (
  Ca (..)
, CCa (..)
, CaVec (..)
, CCaVec (..)
, CaMat (..)
, CCaMat (..)
, CaPoly (..)
, CCaPoly (..)
, CaPolyVec (..)
, CCaPolyVec (..)
, CaFactor (..)
, CCaFactor (..)
, CaCtx (..)
, CCaCtx (..)
, CaField (..)
, CCaField (..)
, CaFieldCache (..)
, CCaFieldCache (..)
, CaExt (..)
, CCaExt (..)
, CaExtCache (..)
, CCaExtCache (..)
, CFexpr
) where

import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.Types
import Data.Number.Flint.Flint

data Ca = Ca {-# UNPACK #-} !(ForeignPtr CCa)
type CCa = CFlint Ca

data CaFactor = CaFactor {-# UNPACK #-} !(ForeignPtr CCaFactor)
type CCaFactor = CFlint CaFactor

data CaCtx = CaCtx {-# UNPACK #-} !(ForeignPtr CCaCtx)
type CCaCtx = CFlint CaCtx

data CaVec = CaVec {-# UNPACK #-} !(ForeignPtr CCaVec)
type CCaVec = CFlint CaVec

data CaMat = CaMat {-# UNPACK #-} !(ForeignPtr CCaMat)
data CCaMat = CCaMat (Ptr CCa) CLong CLong (Ptr CCa)

data CaPoly = CaPoly {-# UNPACK #-} !(ForeignPtr CCaPoly)
type CCaPoly = CFlint CaPoly

data CaPolyVec = CaPolyVec {-# UNPACK #-} !(ForeignPtr CCaPolyVec)
type CCaPolyVec = CFlint CaPolyVec

data CaField = CaField {-# UNPACK #-} !(ForeignPtr CCaField)
type CCaField = CFlint CaField

data CaFieldCache = CaFieldCache {-# UNPACK #-} !(ForeignPtr CCaFieldCache)
type CCaFieldCache = CFlint CaFieldCache

data CaExt = CaExt {-# UNPACK #-} !(ForeignPtr CCaExt)
type CCaExt = CFlint CaExt

data CaExtCache = CaExtCache {-# UNPACK #-} !(ForeignPtr CCaExtCache)
type CCaExtCache = CFlint CaExtCache

data CFexpr
