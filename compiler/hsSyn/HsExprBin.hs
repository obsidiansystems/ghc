module HsExprBin
  ( getModuleSplicesPath
  , whenSet
  , HsSpliceData(..)
  , nonEmptyHsSpliceData
  , emptyHsSpliceData
  , SpliceResult(..)
  , recordSpliceResult
  , lookupSpliceResult
  , exprSE2PS
  , declSE2PS
  , exprPS2SE
  , declPS2SE
  , handleUnsupported
  ) where

import Binary
import GhcPrelude
import HsDecls
import HsExpr
import HsExprBin_Conversions
import HsExprBin_Instances ()
import HsExtension
import Module
import Outputable
import SrcLoc
import TcRnTypes

import qualified Data.Map.Strict as Map
import System.FilePath

-- * .hs-splice file contents

getModuleSplicesPath :: FilePath -> Module -> FilePath
getModuleSplicesPath splicesDir m = splicesDir
  </> toPath (moduleNameString (moduleName m)) <.> "hs-splice"

  where toPath = map (\c -> if c == '.' then '/' else c)

whenSet :: Monad m => Maybe a -> (a -> m b) -> m b -> m b
whenSet m j n = maybe n j m

newtype HsSpliceData = HsSpliceData { hsSpliceMap :: Map.Map SrcSpan SpliceResult }

emptyHsSpliceData :: HsSpliceData
emptyHsSpliceData = HsSpliceData Map.empty

nonEmptyHsSpliceData :: HsSpliceData -> Bool
nonEmptyHsSpliceData = not . Map.null . hsSpliceMap

data SpliceResult
  = SRExpr  (LHsExpr GhcSe)
  | SRDecls [LHsDecl GhcSe] -- TODO: change to HsGroup ?
  -- TODO: add patterns and types?

instance Binary SpliceResult where
  put_ bh r = case r of
    SRExpr e -> putByte bh 0 >> put_ bh e
    SRDecls ds -> putByte bh 1 >> put_ bh ds
  get bh = do
    tag <- getByte bh
    case tag of
      0 -> SRExpr <$> get bh
      1 -> SRDecls <$> get bh
      _ -> panic "Binary SpliceResult: unknown tag"

instance Binary HsSpliceData where
  put_ bh (HsSpliceData m) = put_ bh (Map.toList m)
  get bh = (\l -> HsSpliceData (Map.fromList l)) <$> get bh

recordSpliceResult :: SrcSpan -> SpliceResult -> HsSpliceData -> HsSpliceData
recordSpliceResult loc res (HsSpliceData m) = HsSpliceData (Map.insert loc res m)

lookupSpliceResult :: SrcSpan -> HsSpliceData -> Maybe SpliceResult
lookupSpliceResult loc (HsSpliceData m) = Map.lookup loc m

-- * High-level conversion interface

-- Converting Se -> Ps

exprSE2PS :: LHsExpr GhcSe -> RnM (ConvResult (LHsExpr GhcPs))
exprSE2PS = runConv . cvLHsExpr

declSE2PS :: LHsDecl GhcSe -> RnM (ConvResult (LHsDecl GhcPs))
declSE2PS = runConv . cvLHsDecl

-- Converting Ps -> Se

exprPS2SE :: LHsExpr GhcPs -> RnM (ConvResult (LHsExpr GhcSe))
exprPS2SE = runConv . cvLHsExpr

declPS2SE :: LHsDecl GhcPs -> RnM (ConvResult (LHsDecl GhcSe))
declPS2SE = runConv . cvLHsDecl

-- * Error reporting

-- | Panics with a nice error when we encounter an unsupported
--   construct, or returns the actual result if the conversion
--   succeeded.
handleUnsupported
  :: Located SDoc -- ^ TH expression that got evaluated
  -> Maybe SDoc -- ^ code resulting from the evaluation of the 1st arg
  -> ConvResult a -- ^ result of the conversion
  -> RnM a
handleUnsupported (L loc thDoc) resDoc convRes = case convRes of
  ConvOK a -> pure a
  ConvError (ConvUnsupported conName tyName subexprDoc) ->
    pprPanic "HsExprBin.handleUnsupported" . vcat $
      [ text "GHC encountered a Haskell construct not supported by -{load, save}-splices:"
      , nest 4 $ subexprDoc <> text (" - constructor " ++ conName ++ " of type " ++ tyName)
      , text "while evaluating the following expression from "  <> ppr loc <> text ":"
      , nest 4 $ thDoc
      ] ++
      maybe [] (\d -> [text "which resulted in:" , nest 4 d]) resDoc

  ConvError (ConvFailure errorStr) -> panic errorStr
