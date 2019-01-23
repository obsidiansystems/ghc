{-# LANGUAGE ConstraintKinds, DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies, TypeSynonymInstances #-}
module HsExprBin_Conversions where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Data.Char (isDigit)
import Data.List (intercalate)
import Data.Maybe
import Data.Traversable

import Bag (mapBagM)
import Class
import CoreSyn ( Tickish(..) )
import DynFlags
import FastString
import GhcPrelude
import HsBinds
import HsDecls
import HsExpr
import HsExtension
import HsLit
import HsPat
import HsTypes
import Module
import Name
import Outputable
import PackageConfig
import Packages
import PlaceHolder
import RdrName
import SeName
import SrcLoc
import TcRnTypes
import IfaceType
import ToIface (toIfaceType)
import TyCoRep (Type(..), TyLit(..))

data ConvError
  = ConvUnsupported String String SDoc
  -- constructor name, type name, text rendering
  -- of the unsupported subexpression
  | ConvFailure String

data ConvResult a
  = ConvError ConvError
  | ConvOK a
  deriving Functor
-- * Conversion utilities

newtype Conv a = Conv { runConv :: RnM (ConvResult a) }

instance Functor Conv where
  fmap f (Conv k) = Conv (fmap (fmap f) k)

instance Applicative Conv where
  pure = Conv . return . ConvOK
  (<*>) = ap

instance Monad Conv where
  return = pure

  Conv mx >>= f = Conv $ mx >>= \cvx -> case cvx of
    ConvOK x    -> runConv (f x)
    ConvError e -> pure (ConvError e)

unsupported :: String -- ^ constructor name
            -> String -- ^ type name
            -> SDoc   -- ^ textual rendering of the unsupported subexpression
            -> Conv a
unsupported con ty subexpr = Conv $
  pure (ConvError $ ConvUnsupported con ty subexpr)

badInput :: String -> Conv a
badInput str = Conv $ pure (ConvError $ ConvFailure str)

liftRn :: RnM a -> Conv a
liftRn = Conv . fmap ConvOK

class ConvertType t u where
  convertType :: t -> Conv u

class ConvertName a b where
  convertName :: a -> Conv b

instance ConvertName a b => ConvertName (Located a) (Located b) where
  convertName = traverse convertName

instance ConvertName a b => ConvertName [a] [b] where
  convertName = traverse convertName

instance ConvertName a b => ConvertName (Either e a) (Either e b) where
  convertName = traverse convertName

instance ConvertName a b => ConvertName (HsMatchContext a) (HsMatchContext b) where
  convertName = traverse convertName

instance ConvertName a b => ConvertName (HsStmtContext a) (HsStmtContext b) where
  convertName = traverse convertName

instance ConvertName a b => ConvertName (Maybe a) (Maybe b) where
  convertName = traverse convertName

instance ConvertType a a where
  convertType = pure

instance ConvertType Type IfaceType where
  convertType = pure . toIfaceType

instance ConvertType IfaceType Type where
  convertType (IfaceLitTy n) = pure $ LitTy (go n)
    where go (IfaceNumTyLit a) = NumTyLit a
          go (IfaceStrTyLit a) = StrTyLit a
  convertType e@(IfaceFreeTyVar {}) = unsupported "IfaceFreeTyVar" "IfaceType" (ppr e)
  convertType e@(IfaceTyVar {}) = unsupported "IfaceTyVar" "IfaceType" (ppr e)
  convertType e@(IfaceAppTy {}) = unsupported "IfaceAppTy" "IfaceType" (ppr e)
  convertType e@(IfaceFunTy {}) = unsupported "IfaceFunTy" "IfaceType" (ppr e)
  convertType e@(IfaceDFunTy {}) = unsupported "IfaceDFunTy" "IfaceType" (ppr e)
  convertType e@(IfaceForAllTy {}) = unsupported "IfaceForAllTy" "IfaceType" (ppr e)
  convertType e@(IfaceTyConApp {}) = unsupported "IfaceTyConApp" "IfaceType" (ppr e)
  convertType e@(IfaceCastTy {}) = unsupported "IfaceCastTy" "IfaceType" (ppr e)
  convertType e@(IfaceCoercionTy {}) = unsupported "IfaceCoercion" "IfaceType" (ppr e)
  convertType e@(IfaceTupleTy {}) = unsupported "IfaceTupleTy" "IfaceType" (ppr e)


instance ConvertName RdrName SeName where
  convertName = pure . mkSeName

instance ConvertName SeName RdrName where
  convertName (SeName n) = case n of
    Orig mod occn -> do
      -- TODO: introduce some caching here, to avoid doing the
      --       searchPackageId dance too often.
      currentMod <- liftRn getModule

      if samePackages currentMod mod
        then let newMod = mod { moduleUnitId = moduleUnitId currentMod } in
               pure (Orig newMod occn)
        else do mnewmod <- liftRn (findEquivalentModule mod)
                case mnewmod of
                  Nothing   -> pure (Orig mod occn)
                  Just mod' -> pure (Orig mod' occn)

    _             -> pure n

    where samePackages mod1 mod2 = fromMaybe False $ do -- maybe monad
            let str1 = unitIdString (moduleUnitId mod1)
                str2 = unitIdString (moduleUnitId mod2)
            (pkg1, ver1, _mhash1) <- parseUnitId' str1
            (pkg2, ver2, _mhash2) <- parseUnitId' str2
            return (pkg1 == pkg2 && ver1 == ver2)

instance ConvertName Name SeName where
  convertName n = pure $ mkSeName (nameRdrName n)

instance ConvertName SeName Name where
  convertName (SeName n) = case isExact_maybe n of
    Just a -> pure a
    _      -> badInput "convertName :: SeName -> Name: non exact RdrName in SeName"

type TypeConstraints p q =
  ( ConvertType (LitType p) (LitType q)
  , ConvertName (IdP p) (IdP q)
  , ConvertName (DoName p) (DoName q)
  , ConvertName (NameOrRdrName (IdP p)) (NameOrRdrName (IdP q))
  , ConvertName (RdrOrSeName p) (RdrOrSeName q)
  , ConvertIdX p q
  , OutputableBndrId p
  , TTGConstraints1 p q
  , TTGConstraints2 p q
  , TTGConstraints3 p q
  , TTGConstraints4 p q
  , TTGConstraints5 p q
  )

type TTGConstraints1 p q =
  ( XTyClD p ~ XTyClD q
  , XInstD p ~ XInstD q
  , XDerivD p ~ XDerivD q
  , XValD p ~ XValD q
  , XSigD p ~ XSigD q
  , XDefD p ~ XDefD q
  , XForD p ~ XForD q
  , XWarningD p ~ XWarningD q
  , XRoleAnnotD p ~ XRoleAnnotD q
  , XAnnD p ~ XAnnD q
  , XRuleD p ~ XRuleD q
  , XSpliceD p ~ XSpliceD q
  , XDocD p ~ XDocD q
  , XHsAnnotation p ~ XHsAnnotation q
  , XClsInstD p ~ XClsInstD q
  , XDataFamInstD p ~ XDataFamInstD q
  , XTyFamInstD p ~ XTyFamInstD q
  , XCClsInstDecl p ~ XCClsInstDecl q
  , XCDerivDecl p ~ XCDerivDecl q
  , XFamDecl p ~ XFamDecl q
  , XSynDecl p ~ XSynDecl q
  , XDataDecl p ~ XDataDecl q
  , XClassDecl p ~ XClassDecl q
  , XCRoleAnnotDecl p ~ XCRoleAnnotDecl q
  , XCRuleDecls p ~ XCRuleDecls q
  , XHsRule p ~ XHsRule q
  , XSpliceDecl p ~ XSpliceDecl q
  , XTypedSplice p ~ XTypedSplice q
  , XUntypedSplice p ~ XUntypedSplice q
  , XQuasiQuote p ~ XQuasiQuote q
  , XCRuleBndr p ~ XCRuleBndr q
  , XRuleBndrSig p ~ XRuleBndrSig q
  , XCFamEqn p (LHsQTyVars p) (LHsType p)
      ~ XCFamEqn q (LHsQTyVars q) (LHsType q)
  , XCFamilyDecl p ~ XCFamilyDecl q
  , XNoSig p ~ XNoSig q
  , XCKindSig p ~ XCKindSig q
  , XTyVarSig p ~ XTyVarSig q
  , XCFamEqn p (HsTyPats p) (HsType p)
     ~ XCFamEqn q (HsTyPats q) (LHsType q)
  , XHsQTvs p ~ XHsQTvs q
  , XForeignImport p ~ XForeignImport q
  , XForeignExport p ~ XForeignExport q
  , XCDefaultDecl p ~ XCDefaultDecl q
  , XCFamEqn p (HsTyPats p) (HsDataDefn p)
      ~ XCFamEqn q (HsTyPats q) (HsDataDefn q)
  , XCHsDataDefn p ~ XCHsDataDefn q
  , XConDeclGADT p ~ XConDeclGADT q
  , XConDeclH98 p ~ XConDeclH98 q
  , XCHsDerivingClause p ~ XCHsDerivingClause q
  , XConDeclField p ~ XConDeclField q
  )

type TTGConstraints2 p q =
  ( XWarnings p ~ XWarnings q
  , XWarning p ~ XWarning q
  , XVar p ~ XVar q
  , XUnboundVar p ~ XUnboundVar q
  , XConLikeOut p ~ XConLikeOut q
  , XRecFld p ~ XRecFld q
  , XOverLabel p ~ XOverLabel q
  , XIPVar p ~ XIPVar q
  , XOverLitE p ~ XOverLitE q
  , XLitE p ~ XLitE q
  , XLam p ~ XLam q
  , XLamCase p ~ XLamCase q
  , XApp p ~ XApp q
  , XAppTypeE p ~ XAppTypeE q
  , XOpApp p ~ XOpApp q
  , XNegApp p ~ XNegApp q
  , XPar p ~ XPar q
  , XSectionL p ~ XSectionL q
  , XSectionR p ~ XSectionR q
  , XExplicitTuple p ~ XExplicitTuple q
  , XExplicitSum p ~ XExplicitSum q
  , XExplicitList p ~ XExplicitList q
  , XCase p ~ XCase q
  , XIf p ~ XIf q
  , XMultiIf p ~ XMultiIf q
  , XLet p ~ XLet q
  , XDo p ~ XDo q
  , XRecordUpd p ~ XRecordUpd q
  , XExprWithTySig p ~ XExprWithTySig q
  , XArithSeq p ~ XArithSeq q
  , XSCC p ~ XSCC q
  , XCoreAnn p ~ XCoreAnn q
  , XStatic p ~ XStatic q
  , XEWildPat p ~ XEWildPat q
  , XEAsPat p ~ XEAsPat q
  , XEViewPat p ~ XEViewPat q
  , XELazyPat p ~ XELazyPat q
  , XProc p ~ XProc q
  , XBinTick p ~ XBinTick q
  , XTickPragma p ~ XTickPragma q
  , XSpliceE p ~ XSpliceE q
  , XBracket p ~ XBracket q
  , XTick p ~ XTick q
  , XRecordCon p ~ XRecordCon q
  , XExpBr p ~ XExpBr q
  , XPatBr p ~ XPatBr q
  , XDecBrL p ~ XDecBrL q
  , XDecBrG p ~ XDecBrG q
  , XTypBr p ~ XTypBr q
  , XVarBr p ~ XVarBr q
  , XTExpBr p ~ XTExpBr q
  , XCHsGroup p ~ XCHsGroup q
  , XCTyClGroup p ~ XCTyClGroup q
  , XCmdTop p ~ XCmdTop q
  , XCmdArrApp p ~ XCmdArrApp q
  , XCmdArrForm p ~ XCmdArrForm q
  , XCmdApp p ~ XCmdApp q
  , XCmdLam p ~ XCmdLam q
  , XCmdPar p ~ XCmdPar q
  , XCmdCase p ~ XCmdCase q
  , XCmdIf p ~ XCmdIf q
  , XCmdLet p ~ XCmdLet q
  )

type TTGConstraints3 p q =
  ( XCmdDo p ~ XCmdDo q
  , XPresent p ~ XPresent q
  , XMissing p ~ XMissing q
  , XUnambiguous p ~ XUnambiguous q
  , XAmbiguous p ~ XAmbiguous q
  , XOverLit p ~ XOverLit q
  , XMG p (LHsExpr p) ~ XMG q (LHsExpr q)
  , XMG p (LHsCmd p) ~ XMG q (LHsCmd q)
  , XCMatch p (LHsExpr p) ~ XCMatch q (LHsExpr q)
  , XCMatch p (LHsCmd p) ~ XCMatch q (LHsCmd q)
  , XWildPat p ~ XWildPat q
  , XVarPat p ~ XVarPat q
  , XLazyPat p ~ XLazyPat q
  , XAsPat p ~ XAsPat q
  , XParPat p ~ XParPat q
  , XBangPat p ~ XBangPat q
  , XListPat p ~ XListPat q
  , XTuplePat p ~ XTuplePat q
  , XSumPat p ~ XSumPat q
  , XViewPat p ~ XViewPat q
  , XLitPat p ~ XLitPat q
  , XNPat p ~ XNPat q
  , XNPlusKPat p ~ XNPlusKPat q
  , XSigPat p ~ XSigPat q
  , XSplicePat p ~ XSplicePat q
  , XCGRHSs p (LHsExpr p) ~ XCGRHSs q (LHsExpr q)
  , XCGRHSs p (LHsCmd p) ~ XCGRHSs q (LHsCmd q)
  , XCGRHS p (LHsExpr p) ~ XCGRHS q (LHsExpr q)
  , XCGRHS p (LHsCmd p) ~ XCGRHS q (LHsCmd q)
  , XHsValBinds p p ~ XHsValBinds q q
  , XHsIPBinds p p ~ XHsIPBinds q q
  , XEmptyLocalBinds p p ~ XEmptyLocalBinds q q
  , XValBinds p p ~ XValBinds q q
  , XCFieldOcc p ~ XCFieldOcc q
  , XParStmt p p (LHsExpr p) ~ XParStmt q q (LHsExpr q)
  , XRecStmt p p (LHsExpr p) ~ XRecStmt q q (LHsExpr q)
  , XLetStmt p p (LHsExpr p) ~ XLetStmt q q (LHsExpr q)
  , XApplicativeStmt p p (LHsExpr p)
      ~ XApplicativeStmt q q (LHsExpr q)
  , XBodyStmt p p (LHsExpr p) ~ XBodyStmt q q (LHsExpr q)
  , XBindStmt p p (LHsExpr p) ~ XBindStmt q q (LHsExpr q)
  , XLastStmt p p (LHsExpr p) ~ XLastStmt q q (LHsExpr q)
  , XTransStmt p p (LHsExpr p) ~ XTransStmt q q (LHsExpr q)
  , XParStmt p p (LHsCmd p) ~ XParStmt q q (LHsCmd q)
  , XRecStmt p p (LHsCmd p) ~ XRecStmt q q (LHsCmd q)
  , XLetStmt p p (LHsCmd p) ~ XLetStmt q q (LHsCmd q)
  , XApplicativeStmt p p (LHsCmd p)
      ~ XApplicativeStmt q q (LHsCmd q)
  , XBodyStmt p p (LHsCmd p) ~ XBodyStmt q q (LHsCmd q)
  , XBindStmt p p (LHsCmd p) ~ XBindStmt q q (LHsCmd q)
  , XLastStmt p p (LHsCmd p) ~ XLastStmt q q (LHsCmd q)
  , XTransStmt p p (LHsCmd p) ~ XTransStmt q q (LHsCmd q)
  , XParStmtBlock p p ~ XParStmtBlock q q
  , XIPBinds p ~ XIPBinds q
  , XCIPBind p ~ XCIPBind q
  , XFunBind p p ~ XFunBind q q
  , XPatBind p p ~ XPatBind q q
  , XVarBind p p ~ XVarBind q q
  , XPatSynBind p p ~ XPatSynBind q q
  , XHsWC p (HsImplicitBndrs p (LHsType p))
      ~ XHsWC q (HsImplicitBndrs q (LHsType q))
  , XHsWC p (LHsType p) ~ XHsWC q (LHsType q)
  , XHsIB p (LHsType p)
      ~ XHsIB q (LHsType q)
  , XHsIB p (FamEqn p (HsTyPats p) (LHsType p))
      ~ XHsIB q (FamEqn q (HsTyPats q) (LHsType q))
  , XHsIB p (FamEqn p (HsTyPats p) (HsDataDefn p))
      ~ XHsIB q (FamEqn q (HsTyPats q) (HsDataDefn q))
  )

type TTGConstraints4 p q =
  ( XForAllTy p ~ XForAllTy q
  , XQualTy p ~ XQualTy q
  , XTyVar p ~ XTyVar q
  , XAppTy p ~ XAppTy q
  , XFunTy p ~ XFunTy q
  , XListTy p ~ XListTy q
  , XTupleTy p ~ XTupleTy q
  , XSumTy p ~ XSumTy q
  , XOpTy p ~ XOpTy q
  , XParTy p ~ XParTy q
  , XIParamTy p ~ XIParamTy q
  , XKindSig p ~ XKindSig q
  , XBangTy p ~ XBangTy q
  , XRecTy p ~ XRecTy q
  , XExplicitListTy p ~ XExplicitListTy q
  , XExplicitTupleTy p ~ XExplicitTupleTy q
  , XTyLit p ~ XTyLit q
  , XWildCardTy p ~ XWildCardTy q
  , XDocTy p ~ XDocTy q
  , XSpliceTy p ~ XSpliceTy q
  , XUserTyVar p ~ XUserTyVar q
  , XKindedTyVar p ~ XKindedTyVar q
  , XApplicativeArgOne p ~ XApplicativeArgOne q
  , XApplicativeArgMany p ~ XApplicativeArgMany q
  , XTypeSig p ~ XTypeSig q
  , XPatSynSig p ~ XPatSynSig q
  , XClassOpSig p ~ XClassOpSig q
  , XInlineSig p ~ XInlineSig q
  , XFixSig p ~ XFixSig q
  , XSpecSig p ~ XSpecSig q
  , XSpecInstSig p ~ XSpecInstSig q
  , XSCCFunSig p ~ XSCCFunSig q
  , XCompleteMatchSig p ~ XCompleteMatchSig q
  , XMinimalSig p ~ XMinimalSig q
  , XFixitySig p ~ XFixitySig q
  , XPSB p p ~ XPSB q q
  , XXHsDecl p ~ XXHsDecl q
  , XXAnnDecl p ~ XXAnnDecl q
  , XXInstDecl p ~ XXInstDecl q
  , XXClsInstDecl p ~ XXClsInstDecl q
  , XXDerivDecl p ~ XXDerivDecl q
  , XXTyClDecl p ~ XXTyClDecl q
  , XXRoleAnnotDecl p ~ XXRoleAnnotDecl q
  , XXRuleDecls p ~ XXRuleDecls q
  , XXRuleDecl p ~ XXRuleDecl q
  , XXSpliceDecl p ~ XXSpliceDecl q
  , XXSplice p ~ XXSplice q
  , XXRuleBndr p ~ XXRuleBndr q
  , XXFamilyDecl p ~ XXFamilyDecl q
  , XXFamEqn p (LHsQTyVars p) (LHsType p)
      ~ XXFamEqn q (LHsQTyVars q) (LHsType q)
  , XXFamEqn p (HsTyPats p) (LHsType p)
      ~ XXFamEqn q (HsTyPats q) (LHsType q)
  , XXFamEqn p (HsTyPats p) (HsDataDefn p)
      ~ XXFamEqn q (HsTyPats q) (HsDataDefn q)
  , XXFamilyResultSig p ~ XXFamilyResultSig q
  , XXLHsQTyVars p ~ XXLHsQTyVars q
  , XXForeignDecl p ~ XXForeignDecl q
  , XXDefaultDecl p ~ XXDefaultDecl q
  , XXHsDataDefn p ~ XXHsDataDefn q
  , XXConDecl p ~ XXConDecl q
  , XXHsDerivingClause p ~ XXHsDerivingClause q
  , XXConDeclField p ~ XXConDeclField q
  , XXWarnDecls p ~ XXWarnDecls q
  , XXWarnDecl p ~ XXWarnDecl q
  )

type TTGConstraints5 p q =
  ( XXExpr p ~ XXExpr q
  , XXBracket p ~ XXBracket q
  , XXHsGroup p ~ XXHsGroup q
  , XXTyClGroup p ~ XXTyClGroup q
  , XXCmdTop p ~ XXCmdTop q
  , XXCmd p ~ XXCmd q
  , XXTupArg p ~ XXTupArg q
  , XXAmbiguousFieldOcc p ~ XXAmbiguousFieldOcc q
  , XXOverLit p ~ XXOverLit q
  , XXMatchGroup p (LHsExpr p) ~ XXMatchGroup q (LHsExpr q)
  , XXMatchGroup p (LHsCmd p) ~ XXMatchGroup q (LHsCmd q)
  , XXPat p ~ Located (Pat p)
  , XXPat q ~ Located (Pat q)
  , XXMatch p (LHsExpr p) ~ XXMatch q (LHsExpr q)
  , XXMatch p (LHsCmd p) ~ XXMatch q (LHsCmd q)
  , XXGRHSs p (LHsExpr p) ~ XXGRHSs q (LHsExpr q)
  , XXGRHSs p (LHsCmd p) ~ XXGRHSs q (LHsCmd q)
  , XXGRHS p (LHsExpr p) ~ XXGRHS q (LHsExpr q)
  , XXGRHS p (LHsCmd p) ~ XXGRHS q (LHsCmd q)
  , XXHsLocalBindsLR p p ~ XXHsLocalBindsLR q q
  , XXFieldOcc p ~ XXFieldOcc q
  , XXParStmtBlock p p ~ XXParStmtBlock q q
  , XXStmtLR p p (LHsExpr p) ~ XXStmtLR q q (LHsExpr q)
  , XXStmtLR p p (LHsCmd p) ~ XXStmtLR q q (LHsCmd q)
  , XXHsIPBinds p ~ XXHsIPBinds q
  , XXIPBind p ~ XXIPBind q
  , XXHsWildCardBndrs p (HsImplicitBndrs p (LHsType p))
  ~ XXHsWildCardBndrs q (HsImplicitBndrs q (LHsType q))
  , XXHsBindsLR p p ~ XXHsBindsLR q q
  , XXHsWildCardBndrs p (LHsType p)
  ~ XXHsWildCardBndrs q (LHsType q)
  , XStarTy p ~ XStarTy q
  , XXType p ~ XXType q
  , XXTyVarBndr p ~ XXTyVarBndr q
  , XXApplicativeArg p ~ XXApplicativeArg q
  , XXSig p ~ XXSig q
  , XXHsImplicitBndrs p (LHsType p)
  ~ XXHsImplicitBndrs q (LHsType q)
  , XXHsImplicitBndrs p (FamEqn p (HsTyPats p) (LHsType p))
  ~ XXHsImplicitBndrs q (FamEqn q (HsTyPats q) (LHsType q))
  , XXHsImplicitBndrs p (FamEqn p (HsTyPats p) (HsDataDefn p))
  ~ XXHsImplicitBndrs q (FamEqn q (HsTyPats q) (HsDataDefn q))
  , XXFixitySig p ~ XXFixitySig q
  , XXPatSynBind p p ~ XXPatSynBind q q
  , NoGhcTc p ~ p
  , NoGhcTc q ~ q
  , XCFamEqn p (HsTyPats p) (LHsType p)
  ~ XCFamEqn q (HsTyPats q) (LHsType q)
  , XViaStrategy p ~ LHsSigType p
  , XViaStrategy q ~ LHsSigType q
  , XAppKindTy p ~ XAppKindTy q
  )

-- * Actual conversion implementation

-- declarations

cvLHsDecl :: TypeConstraints p q => LHsDecl p -> Conv (LHsDecl  q)
cvLHsDecl = traverse cvHsDecl

cvHsDecl :: TypeConstraints p q => HsDecl p -> Conv (HsDecl  q)
cvHsDecl (TyClD a b) = TyClD <$> pure a <*> cvTyClDecl b
cvHsDecl (InstD a b) = InstD <$> pure a <*> cvInstDecl b
cvHsDecl (DerivD a b) = DerivD <$> pure a <*> cvDerivDecl b
cvHsDecl (ValD a b) = ValD <$> pure a <*> cvHsBindLR b
cvHsDecl (SigD a b) = SigD <$> pure a <*> cvSig b
cvHsDecl (DefD a b) = DefD <$> pure a <*> cvDefaultDecl b
cvHsDecl (ForD a b) = ForD <$> pure a <*> cvForeignDecl b
cvHsDecl (WarningD a b) = WarningD <$> pure a <*> cvWarningDecls b
cvHsDecl (RoleAnnotD a b) = RoleAnnotD <$> pure a <*> cvRoleAnnotDecl b
cvHsDecl (AnnD a b) = AnnD <$> pure a <*> cvAnnDecl b
cvHsDecl (RuleD a b) = RuleD <$> pure a <*> cvRuleDecls b
cvHsDecl (SpliceD a b) = SpliceD <$> pure a <*> cvSpliceDecl b
cvHsDecl (DocD a b) = pure (DocD a b)
cvHsDecl (XHsDecl a) = pure (XHsDecl a)

cvAnnDecl :: TypeConstraints p q => AnnDecl p -> Conv (AnnDecl  q)
cvAnnDecl (HsAnnotation a b c d) =
  HsAnnotation a b <$> cvAnnProvenance c <*> cvLHsExpr d
cvAnnDecl (XAnnDecl a) = pure (XAnnDecl a)

cvInstDecl :: TypeConstraints p q => InstDecl p -> Conv (InstDecl  q)
cvInstDecl (ClsInstD a b) = ClsInstD a <$> cvClsInstDecl b
cvInstDecl (DataFamInstD a b) = DataFamInstD a <$> cvDataFamInstDecl b
cvInstDecl (TyFamInstD a b) = TyFamInstD a <$> cvTyFamInstDecl b
cvInstDecl (XInstDecl a) = pure (XInstDecl a)

cvClsInstDecl :: TypeConstraints p q => ClsInstDecl p -> Conv (ClsInstDecl  q)
cvClsInstDecl (ClsInstDecl a b c d e f g) =
  ClsInstDecl a
    <$> cvHsImplicitBndrs (traverse cvType) b
    <*> mapBagM (traverse cvHsBindLR) c
    <*> traverse (traverse cvSig) d
    <*> traverse (traverse cvTyFamInstDecl) e
    <*> traverse (traverse cvDataFamInstDecl) f
    <*> pure g
cvClsInstDecl (XClsInstDecl a) = pure (XClsInstDecl a)

cvDerivDecl :: TypeConstraints p q => DerivDecl p -> Conv (DerivDecl  q)
cvDerivDecl (DerivDecl a b c d) =
  DerivDecl a <$> cvHsWildCardBndrs (cvHsImplicitBndrs $ traverse cvType) b
              <*> traverse (traverse cvDerivStrategy) c
              <*> pure d
cvDerivDecl (XDerivDecl a) = pure (XDerivDecl a)

cvDerivStrategy
  :: TypeConstraints p q => DerivStrategy p -> Conv (DerivStrategy  q)
cvDerivStrategy StockStrategy = pure StockStrategy
cvDerivStrategy AnyclassStrategy = pure AnyclassStrategy
cvDerivStrategy NewtypeStrategy = pure NewtypeStrategy
cvDerivStrategy (ViaStrategy a) = ViaStrategy
  <$> cvHsImplicitBndrs (traverse cvType) a

cvTyClDecl :: TypeConstraints p q => TyClDecl p -> Conv (TyClDecl  q)
cvTyClDecl (FamDecl a b) = FamDecl <$> pure a <*> cvFamilyDecl b
cvTyClDecl (SynDecl a b c d e) =
  SynDecl a
    <$> convertName b
    <*> cvLHsQTyVars c <*> pure d
    <*> traverse cvType e
cvTyClDecl (DataDecl a b c d e) =
  DataDecl a
    <$> convertName b
    <*> cvLHsQTyVars c <*> pure d
    <*> cvHsDataDefn e
cvTyClDecl (ClassDecl a b c d e f g h i j k) =
  ClassDecl a
    <$> traverse (traverse (traverse cvType)) b
    <*> convertName c
    <*> cvLHsQTyVars d
    <*> pure e
    <*> traverse (traverse cvFunDep) f
    <*> traverse (traverse cvSig) g
    <*> mapBagM (traverse cvHsBindLR) h
    <*> traverse (traverse cvFamilyDecl) i
    <*> traverse (traverse $ cvFamEqn cvLHsQTyVars (traverse cvType)) j
    <*> pure k
cvTyClDecl (XTyClDecl a) = pure (XTyClDecl a)

cvRoleAnnotDecl
  :: TypeConstraints p q => RoleAnnotDecl p -> Conv (RoleAnnotDecl  q)
cvRoleAnnotDecl (RoleAnnotDecl a b c) =
  RoleAnnotDecl a <$> convertName b <*> pure c
cvRoleAnnotDecl (XRoleAnnotDecl a) = pure (XRoleAnnotDecl a)

cvRuleDecls :: TypeConstraints p q => RuleDecls p -> Conv (RuleDecls  q)
cvRuleDecls (HsRules a b c) = HsRules a b <$> traverse (traverse cvRuleDecl) c
cvRuleDecls (XRuleDecls a) = pure (XRuleDecls a)

cvRuleDecl :: TypeConstraints p q => RuleDecl p -> Conv (RuleDecl  q)
cvRuleDecl (HsRule a b c d e f g) =
  HsRule a b c <$> traverse (traverse (traverse cvHsTyVarBndr)) d
               <*> traverse (traverse cvRuleBndr) e
               <*> cvLHsExpr f <*> cvLHsExpr g
cvRuleDecl (XRuleDecl a) = pure (XRuleDecl a)

cvSpliceDecl :: TypeConstraints p q => SpliceDecl p -> Conv (SpliceDecl  q)
cvSpliceDecl (SpliceDecl a b c) =
  SpliceDecl a <$> traverse cvHsSplice b <*> pure c
cvSpliceDecl (XSpliceDecl a) = pure (XSpliceDecl a)

cvHsSplice :: TypeConstraints p q => HsSplice p -> Conv (HsSplice  q)
cvHsSplice (HsTypedSplice a b c d) =
  HsTypedSplice a b <$> convertName c <*> cvLHsExpr d
cvHsSplice (HsUntypedSplice a b c d) =
  HsUntypedSplice a b <$> convertName c <*> cvLHsExpr d
cvHsSplice (HsQuasiQuote a b c d e) =
  HsQuasiQuote a <$> convertName b <*> convertName c <*> pure d <*> pure e
cvHsSplice (HsSplicedT a) = pure (HsSplicedT a)
cvHsSplice (HsSpliced {}) =
  unsupported "HsSpliced" "HsSplice" (error "<not printable>")
cvHsSplice (XSplice a) = pure (XSplice a)

cvRuleBndr :: TypeConstraints p q => RuleBndr p -> Conv (RuleBndr  q)
cvRuleBndr (RuleBndr a b) = RuleBndr a <$> convertName b
cvRuleBndr (RuleBndrSig a b c) =
  RuleBndrSig a <$> convertName b <*> cvHsSigWcType c
cvRuleBndr (XRuleBndr a) = pure (XRuleBndr a)

cvFamEqn
  :: ( TypeConstraints p q
     , XCFamEqn p a b ~ XCFamEqn q c d
     , XXFamEqn p a b ~ XXFamEqn q c d
     )
  => (a -> Conv c)
  -> (b -> Conv d)
  -> FamEqn p a b
  -> Conv (FamEqn q c d)
cvFamEqn goPats goRhs (FamEqn a b c d e f) =
  FamEqn a <$> convertName b <*> traverse (traverse (traverse cvHsTyVarBndr)) c
           <*> goPats d <*> pure e <*> goRhs f
cvFamEqn _ _ (XFamEqn a) = pure (XFamEqn a)

cvFamilyDecl :: TypeConstraints p q => FamilyDecl p -> Conv (FamilyDecl  q)
cvFamilyDecl (FamilyDecl a b c d e f g) =
  FamilyDecl a
    <$> cvFamilyInfo b <*> convertName c
    <*> cvLHsQTyVars d <*> pure e
    <*> traverse cvFamilyResultSig f
    <*> traverse (traverse cvInjectivityAnn) g
cvFamilyDecl (XFamilyDecl a) = pure (XFamilyDecl a)

cvAnnProvenance :: ConvertName a b => AnnProvenance a -> Conv (AnnProvenance b)
cvAnnProvenance (ValueAnnProvenance a) = ValueAnnProvenance <$> convertName a
cvAnnProvenance (TypeAnnProvenance a) = TypeAnnProvenance <$> convertName a
cvAnnProvenance ModuleAnnProvenance = pure ModuleAnnProvenance

cvInjectivityAnn
  :: TypeConstraints p q => InjectivityAnn p -> Conv (InjectivityAnn  q)
cvInjectivityAnn (InjectivityAnn a b) =
  InjectivityAnn <$> convertName a <*> convertName b

cvFamilyResultSig
  :: TypeConstraints p q => FamilyResultSig p -> Conv (FamilyResultSig  q)
cvFamilyResultSig (NoSig a) = pure (NoSig a)
cvFamilyResultSig (KindSig a b) = KindSig a <$> traverse cvType b
cvFamilyResultSig (TyVarSig a b) = TyVarSig a <$> traverse cvHsTyVarBndr b
cvFamilyResultSig (XFamilyResultSig a) = pure (XFamilyResultSig a)

cvFamilyInfo
  :: TypeConstraints p q
  => FamilyInfo p -> Conv (FamilyInfo  q)
cvFamilyInfo DataFamily = pure DataFamily
cvFamilyInfo OpenTypeFamily = pure OpenTypeFamily
cvFamilyInfo (ClosedTypeFamily a) =
  ClosedTypeFamily <$> traverse (traverse (traverse (cvFamInstEqn (traverse cvType)))) a

cvFamInstEqn
  :: ( TypeConstraints p q
     , XCFamEqn p (HsTyPats p) a ~ XCFamEqn q (HsTyPats  q) b
     , XHsIB p (FamEqn p (HsTyPats p) a)
     ~ XHsIB q (FamEqn q (HsTyPats  q) b)
     , XXFamEqn p (HsTyPats p) a ~ XXFamEqn q (HsTyPats  q) b
     , XXHsImplicitBndrs p (FamEqn p (HsTyPats p) a)
     ~ XXHsImplicitBndrs q (FamEqn q (HsTyPats  q) b)
     )
  => (a -> Conv b)
  -> FamInstEqn p a
  -> Conv (FamInstEqn q b)
-- cvFamInstEqn f = cvHsImplicitBndrs (cvFamEqn (traverse (traverse cvType)) f)
cvFamInstEqn f = cvHsImplicitBndrs
  (cvFamEqn (traverse $
               cvHsArg (traverse cvType) (traverse cvType)
            )
            f
  )

cvHsArg :: (a -> Conv x) -> (b -> Conv y) -> HsArg a b -> Conv (HsArg x y)
cvHsArg f _ (HsValArg a)  = HsValArg <$> f a
cvHsArg _ g (HsTypeArg b) = HsTypeArg <$> g b
cvHsArg _ _ (HsArgPar a) = pure (HsArgPar a)

cvFunDep :: ConvertName a b => FunDep a -> Conv (FunDep b)
cvFunDep (xs, ys) = (,) <$> convertName xs <*> convertName ys

cvLHsQTyVars :: TypeConstraints p q => LHsQTyVars p -> Conv (LHsQTyVars  q)
cvLHsQTyVars (HsQTvs a b) = HsQTvs a <$> traverse (traverse cvHsTyVarBndr) b
cvLHsQTyVars (XLHsQTyVars a) = pure (XLHsQTyVars a)

cvForeignDecl :: TypeConstraints p q => ForeignDecl p -> Conv (ForeignDecl  q)
cvForeignDecl (ForeignImport a b c d) =
  ForeignImport a
    <$> convertName b
    <*> cvHsImplicitBndrs (traverse cvType) c
    <*> pure d
cvForeignDecl (ForeignExport a b c d) =
  ForeignExport a
    <$> convertName b
    <*> cvHsImplicitBndrs (traverse cvType) c
    <*> pure d
cvForeignDecl (XForeignDecl a) = pure (XForeignDecl a)

cvDefaultDecl :: TypeConstraints p q => DefaultDecl p -> Conv (DefaultDecl  q)
cvDefaultDecl (DefaultDecl a b) = DefaultDecl a <$> traverse (traverse cvType) b
cvDefaultDecl (XDefaultDecl a) = pure (XDefaultDecl a)

cvTyFamInstDecl
  :: TypeConstraints p q => TyFamInstDecl p -> Conv (TyFamInstDecl  q)
cvTyFamInstDecl (TyFamInstDecl d) =
  TyFamInstDecl <$> cvFamInstEqn (traverse cvType) d

cvDataFamInstDecl
  :: TypeConstraints p q => DataFamInstDecl p -> Conv (DataFamInstDecl  q)
cvDataFamInstDecl (DataFamInstDecl d) =
  DataFamInstDecl <$> cvFamInstEqn cvHsDataDefn d

cvHsDataDefn :: TypeConstraints p q => HsDataDefn p -> Conv (HsDataDefn  q)
cvHsDataDefn (HsDataDefn a b c d e f g) =
  HsDataDefn a b
    <$> traverse (traverse (traverse cvType)) c <*> pure d
    <*> traverse (traverse cvType) e
    <*> traverse (traverse cvConDecl) f <*> cvHsDeriving g
cvHsDataDefn (XHsDataDefn a) = pure (XHsDataDefn a)

cvConDecl :: TypeConstraints p q => ConDecl p -> Conv (ConDecl  q)
cvConDecl (ConDeclGADT a b c d e f g h) =
  ConDeclGADT a
    <$> convertName b
    <*> pure c
    <*> cvLHsQTyVars d
    <*> traverse (traverse (traverse (traverse cvType))) e
    <*> cvHsConDeclDetails f
    <*> traverse cvType g
    <*> pure h
cvConDecl (ConDeclH98 a b c d e f g) =
  ConDeclH98 a
    <$> convertName b
    <*> pure c
    <*> traverse (traverse cvHsTyVarBndr) d
    <*> traverse (traverse (traverse (traverse cvType))) e
    <*> cvHsConDeclDetails f
    <*> pure g
cvConDecl (XConDecl a) = pure (XConDecl a)

cvHsDeriving :: TypeConstraints p q => HsDeriving p -> Conv (HsDeriving  q)
cvHsDeriving = traverse (traverse (traverse cvHsDerivingClause))

cvHsDerivingClause
  :: TypeConstraints p q => HsDerivingClause p -> Conv (HsDerivingClause  q)
cvHsDerivingClause (HsDerivingClause a b c) =
  HsDerivingClause a
    <$> traverse (traverse cvDerivStrategy) b
    <*> traverse (traverse (cvHsImplicitBndrs (traverse cvType))) c
cvHsDerivingClause (XHsDerivingClause a) = pure (XHsDerivingClause a)

cvHsConDeclDetails
  :: TypeConstraints p q => HsConDeclDetails p -> Conv (HsConDeclDetails  q)
cvHsConDeclDetails =
  cvHsConDetails (traverse cvType)
                 (traverse (traverse (traverse cvConDeclField)))

cvHsConDetails
  :: (a -> Conv c) -> (b -> Conv d) -> HsConDetails a b -> Conv (HsConDetails c d)
cvHsConDetails f _  (PrefixCon a) = PrefixCon <$> traverse f a
cvHsConDetails _ g     (RecCon a) = RecCon    <$> g a
cvHsConDetails f _ (InfixCon a b) = InfixCon  <$> f a <*> f b

cvConDeclField :: TypeConstraints p q => ConDeclField p -> Conv (ConDeclField  q)
cvConDeclField (ConDeclField a b c d) =
  ConDeclField a <$> traverse (traverse cvFieldOcc) b <*> traverse cvType c
                 <*> pure d
cvConDeclField (XConDeclField a) = pure (XConDeclField a)

cvWarningDecls :: TypeConstraints p q => WarnDecls p -> Conv (WarnDecls  q)
cvWarningDecls (Warnings a b c) =
  Warnings a b <$> traverse (traverse cvWarningDecl) c
cvWarningDecls (XWarnDecls a) = pure (XWarnDecls a)

cvWarningDecl :: TypeConstraints p q => WarnDecl p -> Conv (WarnDecl  q)
cvWarningDecl (Warning a b c) = Warning a <$> convertName b <*> pure c
cvWarningDecl (XWarnDecl a) = pure (XWarnDecl a)

-- expressions

cvLHsExpr
  :: TypeConstraints p q => LHsExpr p -> Conv (LHsExpr  q)
cvLHsExpr = traverse cvHsExpr

cvHsExpr
  :: TypeConstraints p q => HsExpr p -> Conv (HsExpr  q)
cvHsExpr e = case e of
  HsVar a b -> HsVar a <$> convertName b
  HsUnboundVar a b -> pure (HsUnboundVar a b)
  HsConLikeOut a b -> pure (HsConLikeOut a b)
  HsRecFld a b -> HsRecFld a <$> cvAFieldOcc b
  HsOverLabel a b c -> HsOverLabel a <$> convertName b <*> pure c
  HsIPVar a b -> pure (HsIPVar a b)
  HsOverLit a b -> HsOverLit a <$> cvOverLit b
  HsLit a b -> HsLit a <$> cvLit b
  HsLam a b -> HsLam a <$> cvMatchGroup cvLHsExpr b
  HsLamCase a b -> HsLamCase a <$> cvMatchGroup cvLHsExpr b
  HsApp a b c -> HsApp a <$> cvLHsExpr b <*> cvLHsExpr c
  HsAppType a b c -> HsAppType a <$> cvLHsExpr b <*> cvLHsWcType c
  OpApp a b c d -> OpApp a <$> cvLHsExpr b <*> cvLHsExpr c <*> cvLHsExpr d
  NegApp a b c -> NegApp a <$> cvLHsExpr b <*> cvSyntaxExpr c
  HsPar a b -> HsPar a <$> cvLHsExpr b
  SectionL a b c -> SectionL a <$> cvLHsExpr b <*> cvLHsExpr c
  SectionR a b c -> SectionR a <$> cvLHsExpr b <*> cvLHsExpr c
  ExplicitTuple a b c -> ExplicitTuple a <$> traverse (traverse cvHsTupArg) b
                                         <*> pure c
  ExplicitSum a b c d -> ExplicitSum a b c <$> cvLHsExpr d
  ExplicitList a b c -> ExplicitList a <$> traverse cvSyntaxExpr b <*> traverse cvLHsExpr c
  HsCase a b c -> HsCase a <$> cvLHsExpr b <*> cvMatchGroup cvLHsExpr c
  HsIf a b c d e -> HsIf a <$> traverse cvSyntaxExpr b
                           <*> cvLHsExpr c <*> cvLHsExpr d <*> cvLHsExpr e
  HsMultiIf a b -> HsMultiIf a <$> traverse (traverse (cvGRHS cvLHsExpr)) b
  HsLet a b c -> HsLet a <$> traverse cvHsLocalBinds b <*> cvLHsExpr c
  HsDo a b c -> HsDo a
    <$> convertName b <*> traverse (traverse (traverse (cvStmtLR cvLHsExpr))) c
  RecordCon a b c -> RecordCon a <$> convertName b <*> cvRecordBinds c
  RecordUpd a b c -> RecordUpd a <$> cvLHsExpr b
                                 <*> traverse (traverse cvHsRecUpdField) c
  ExprWithTySig a b c -> ExprWithTySig a <$> cvLHsExpr b <*> cvHsSigWcType c
  ArithSeq a b c -> ArithSeq a <$> traverse cvSyntaxExpr b <*> cvArithSeqInfo c
  HsSCC a b c d -> HsSCC a b c <$> cvLHsExpr d
  HsCoreAnn a b c d -> HsCoreAnn a b c <$> cvLHsExpr d
  HsStatic a b -> HsStatic a <$> cvLHsExpr b
  EWildPat a -> pure (EWildPat a)
  EAsPat a b c -> EAsPat a <$> convertName b <*> cvLHsExpr c
  EViewPat a b c -> EViewPat a <$> cvLHsExpr b <*> cvLHsExpr c
  ELazyPat a b -> ELazyPat a <$> cvLHsExpr b
  HsProc a b c -> HsProc a <$> cvPat b <*> traverse cvHsCmdTop c
  HsBinTick a b c d -> HsBinTick a b c <$> cvLHsExpr d
  HsTickPragma a b c d e -> HsTickPragma a b c d <$> cvLHsExpr e
  HsSpliceE a b -> HsSpliceE a <$> cvHsSplice b
  HsBracket a b -> HsBracket a <$> cvHsBracket b
  HsTick a b c -> HsTick a <$> cvTickish b <*> cvLHsExpr c
  XExpr a -> pure (XExpr a)
  HsArrApp {} -> unsupported "HsArrApp" "HsExpr" (error "<not printable>")
  HsArrForm {} -> unsupported "HsArrForm" "HsExpr" (error "<not printable>")
  HsWrap {} -> unsupported "HsWrap" "HsExpr" (error "<not printable>")
  HsRnBracketOut {} -> unsupported "HsRnBracketOut" "HsExpr" (error "<not printable>")
  HsTcBracketOut {} -> unsupported "HsTcBracketOut" "HsExpr" (error "<not printable>")

cvHsBracket :: TypeConstraints p q => HsBracket p -> Conv (HsBracket  q)
cvHsBracket (ExpBr a b) = ExpBr a <$> cvLHsExpr b
cvHsBracket (PatBr a b) = PatBr a <$> cvPat b
cvHsBracket (DecBrL a b) = DecBrL a <$> traverse (traverse cvHsDecl) b
cvHsBracket (DecBrG a b) = DecBrG a <$> cvHsGroup b
cvHsBracket (TypBr a b) = TypBr a <$> traverse cvType b
cvHsBracket (VarBr a b c) = VarBr a b <$> convertName c
cvHsBracket (TExpBr a b) = TExpBr a <$> cvLHsExpr b
cvHsBracket (XBracket a) = pure (XBracket a)

cvTickish :: ConvertName a b => Tickish a -> Conv (Tickish b)
cvTickish (ProfNote a b c) = pure (ProfNote a b c)
cvTickish (HpcTick a b) = pure (HpcTick a b)
cvTickish (Breakpoint a b) = Breakpoint a <$> convertName b
cvTickish (SourceNote a b) = pure (SourceNote a b)

cvHsGroup :: TypeConstraints p q => HsGroup p -> Conv (HsGroup q)
cvHsGroup (HsGroup a b c d e f g h i j k l) = HsGroup a
  <$> cvHsValBindsLR b <*> traverse (traverse cvSpliceDecl) c
  <*> traverse cvTyClGroup d
  <*> traverse (traverse cvDerivDecl) e
  <*> traverse (traverse cvFixitySig) f
  <*> traverse (traverse cvDefaultDecl) g
  <*> traverse (traverse cvForeignDecl) h
  <*> traverse (traverse cvWarningDecls) i
  <*> traverse (traverse cvAnnDecl) j
  <*> traverse (traverse cvRuleDecls) k
  <*> pure l
cvHsGroup (XHsGroup a) = pure (XHsGroup a)

cvTyClGroup :: TypeConstraints p q => TyClGroup p -> Conv (TyClGroup q)
cvTyClGroup (TyClGroup a b c d) = TyClGroup a
  <$> traverse (traverse cvTyClDecl) b
  <*> traverse (traverse cvRoleAnnotDecl) c
  <*> traverse (traverse cvInstDecl) d
cvTyClGroup (XTyClGroup a) = pure (XTyClGroup a)

cvHsCmdTop :: TypeConstraints p q => HsCmdTop p -> Conv (HsCmdTop q)
cvHsCmdTop (HsCmdTop a b) = HsCmdTop a <$> traverse cvHsCmd b
cvHsCmdTop (XCmdTop a) = pure (XCmdTop a)

cvHsCmd :: TypeConstraints p q => HsCmd p -> Conv (HsCmd  q)
cvHsCmd (HsCmdArrApp a b c d e) = HsCmdArrApp a
  <$> cvLHsExpr b <*> cvLHsExpr c <*> pure d <*> pure e
cvHsCmd (HsCmdArrForm a b c d e) = HsCmdArrForm a
  <$> cvLHsExpr b <*> pure c <*> pure d
  <*> traverse (traverse cvHsCmdTop) e
cvHsCmd (HsCmdApp a b c) = HsCmdApp a <$> traverse cvHsCmd b <*> cvLHsExpr c
cvHsCmd (HsCmdLam a b) = HsCmdLam a <$> cvMatchGroup (traverse cvHsCmd) b
cvHsCmd (HsCmdPar a b) = HsCmdPar a <$> traverse cvHsCmd b
cvHsCmd (HsCmdCase a b c) = HsCmdCase a
  <$> cvLHsExpr b <*> cvMatchGroup (traverse cvHsCmd) c
cvHsCmd (HsCmdIf a b c d e) = HsCmdIf a
  <$> traverse cvSyntaxExpr b
  <*> cvLHsExpr c
  <*> traverse cvHsCmd d
  <*> traverse cvHsCmd e
cvHsCmd (HsCmdLet a b c) = HsCmdLet a
  <$> traverse cvHsLocalBinds b <*> traverse cvHsCmd c
cvHsCmd (HsCmdDo a b) = HsCmdDo a
  <$> traverse (traverse (traverse (cvStmtLR (traverse cvHsCmd)))) b
cvHsCmd (HsCmdWrap {}) = unsupported "HsCmdWrap" "HsCmd" (error "<not printable>")
cvHsCmd (XCmd a) = pure (XCmd a)

cvArithSeqInfo :: TypeConstraints p q => ArithSeqInfo p -> Conv (ArithSeqInfo  q)
cvArithSeqInfo (From e) = From <$> cvLHsExpr e
cvArithSeqInfo (FromThen a b) = FromThen <$> cvLHsExpr a <*> cvLHsExpr b
cvArithSeqInfo (FromTo a b) = FromTo <$> cvLHsExpr a <*> cvLHsExpr b
cvArithSeqInfo (FromThenTo a b c) = FromThenTo <$> cvLHsExpr a <*> cvLHsExpr b <*> cvLHsExpr c

cvHsTupArg :: TypeConstraints p q => HsTupArg p -> Conv (HsTupArg  q)
cvHsTupArg (Present a b) = Present a <$> cvLHsExpr b
cvHsTupArg (Missing a) = pure (Missing a)
cvHsTupArg (XTupArg a) = pure (XTupArg a)

cvAFieldOcc
  :: TypeConstraints p q => AmbiguousFieldOcc p -> Conv (AmbiguousFieldOcc  q)
cvAFieldOcc (Unambiguous a b) = Unambiguous a <$> convertName b
cvAFieldOcc (Ambiguous a b) = Ambiguous a <$> convertName b
cvAFieldOcc (XAmbiguousFieldOcc a) = pure (XAmbiguousFieldOcc a)

cvOverLit :: TypeConstraints p q => HsOverLit p -> Conv (HsOverLit  q)
cvOverLit (OverLit a b c) = OverLit a b <$> cvHsExpr c
cvOverLit (XOverLit a) = pure (XOverLit a)

cvLit :: TypeConstraints p q => HsLit p -> Conv (HsLit  q)
cvLit (HsChar a b) = pure (HsChar a b)
cvLit (HsCharPrim a b) = pure (HsCharPrim a b)
cvLit (HsString a b) = pure (HsString a b)
cvLit (HsStringPrim a b) = pure (HsStringPrim a b)
cvLit (HsInt a b) = pure (HsInt a b)
cvLit (HsIntPrim a b) = pure (HsIntPrim a b)
cvLit (HsWordPrim a b) = pure (HsWordPrim a b)
cvLit (HsInt64Prim a b) = pure (HsInt64Prim a b)
cvLit (HsWord64Prim a b) = pure (HsWord64Prim a b)
cvLit (HsInteger a b c) = HsInteger a b <$> convertType c
cvLit (HsRat a b c) = HsRat a b <$> convertType c
cvLit (HsFloatPrim a b) = pure (HsFloatPrim a b)
cvLit (HsDoublePrim a b) = pure (HsDoublePrim a b)
cvLit (XLit a) = pure (XLit a)

cvMatchGroup
  :: ( TypeConstraints p q, XMG p a ~ XMG q b
     , XCMatch p a ~ XCMatch q b, XCGRHSs p a ~ XCGRHSs q b
     , XCGRHS p a ~ XCGRHS q b, XXMatchGroup p a ~ XXMatchGroup q b
     , XXMatch p a ~ XXMatch q b, XXGRHSs p a ~ XXGRHSs q b
     , XXGRHS p a ~ XXGRHS q b
     )
  => (a -> Conv b) -> MatchGroup p a -> Conv (MatchGroup q b)
cvMatchGroup f (MG a b c) = MG a
  <$> traverse (traverse (traverse (cvMatch f))) b
  <*> pure c
cvMatchGroup _ (XMatchGroup a) = pure (XMatchGroup a)

cvMatch
  :: ( TypeConstraints p q, XCMatch p a ~ XCMatch q b
     , XCGRHSs p a ~ XCGRHSs q b, XCGRHS p a ~ XCGRHS q b
     , XXMatch p a ~ XXMatch q b, XXGRHSs p a ~ XXGRHSs q b
     , XXGRHS p a ~ XXGRHS q b
     )
  => (a -> Conv b) -> Match p a -> Conv (Match q b)
cvMatch f (Match a b c d) = Match a
   <$> convertName b <*> traverse cvPat c <*> cvGRHSs f d
cvMatch _ (XMatch a) = pure (XMatch a)

cvPat :: TypeConstraints p q => Pat p -> Conv (Pat  q)
cvPat (WildPat a) = pure (WildPat a)
cvPat (VarPat a b) = VarPat a <$> convertName b
cvPat (LazyPat a b) = LazyPat a <$> cvPat b
cvPat (AsPat a b c) = AsPat a <$> convertName b <*> cvPat c
cvPat (ParPat a b) = ParPat a <$> cvPat b
cvPat (BangPat a b) = BangPat a <$> cvPat b
cvPat (ListPat a b) = ListPat a
  <$> traverse cvPat b
cvPat (TuplePat a b c) = TuplePat a
  <$> traverse cvPat b
  <*> pure c
cvPat (SumPat a b c d) = SumPat a
  <$> cvPat b
  <*> pure c <*> pure d
cvPat (ConPatIn a b) = ConPatIn <$> convertName a <*> cvHsConPatDetails b
cvPat (ViewPat a b c) = ViewPat a <$> cvLHsExpr b <*> cvPat c
cvPat (LitPat a b) = LitPat a <$> cvLit b
cvPat (NPat a b c d) = NPat a
  <$> traverse cvOverLit b <*> traverse cvSyntaxExpr c
  <*> cvSyntaxExpr d
cvPat (NPlusKPat a b c d e f) = NPlusKPat a
  <$> convertName b
  <*> traverse cvOverLit c <*> cvOverLit d
  <*> cvSyntaxExpr e <*> cvSyntaxExpr f
cvPat (SigPat a b c) = SigPat a <$> cvPat b <*> cvHsSigWcType c
cvPat (SplicePat a b) = SplicePat a <$> cvHsSplice b
cvPat (CoPat {}) = unsupported "CoPat" "Pat" (error "<not printable>")
cvPat (ConPatOut {}) = unsupported "ConPatOut" "Pat" (error "<not printable>")
cvPat (XPat a) = XPat <$> traverse cvPat a

cvGRHSs
  :: ( TypeConstraints p q, XCGRHSs p a ~ XCGRHSs q b
     , XCGRHS p a ~ XCGRHS q b, XXGRHSs p a ~ XXGRHSs q b
     , XXGRHS p a ~ XXGRHS q b
     )
  => (a -> Conv b) -> GRHSs p a -> Conv (GRHSs q b)
cvGRHSs f (GRHSs a b c) = GRHSs a
  <$> traverse (traverse (cvGRHS f)) b
  <*> traverse cvHsLocalBinds c
cvGRHSs _ (XGRHSs a) = pure (XGRHSs a)

cvGRHS
  :: ( TypeConstraints p q, XCGRHS p a ~ XCGRHS q b
     , XXGRHS p a ~ XXGRHS q b
     )
  => (a -> Conv b) -> GRHS p a -> Conv (GRHS q b)
cvGRHS f (GRHS a b c) = GRHS a
  <$> traverse (traverse (cvStmtLR cvLHsExpr)) b <*> f c
cvGRHS _ (XGRHS a) = pure (XGRHS a)

cvHsLocalBinds
  :: TypeConstraints p q
  => HsLocalBinds p -> Conv (HsLocalBinds  q)
cvHsLocalBinds (HsValBinds a b) = HsValBinds a <$> cvHsValBindsLR b
cvHsLocalBinds (HsIPBinds a b) = HsIPBinds a <$> cvHsIPBinds b
cvHsLocalBinds (EmptyLocalBinds a) = pure (EmptyLocalBinds a)
cvHsLocalBinds (XHsLocalBindsLR a) = pure (XHsLocalBindsLR a)

cvHsValBindsLR
  :: TypeConstraints p q
  => HsValBindsLR p p -> Conv (HsValBindsLR q  q)
cvHsValBindsLR (ValBinds a b c) = ValBinds a
  <$> mapBagM (traverse cvHsBindLR) b
  <*> traverse (traverse cvSig) c
cvHsValBindsLR (XValBindsLR _) =
  unsupported "XValBindsLR" "HsValBindsLR" (error "<not printable>")

cvHsConPatDetails
  :: TypeConstraints p q => HsConPatDetails p -> Conv (HsConPatDetails  q)
cvHsConPatDetails (PrefixCon a) = PrefixCon <$> traverse cvPat a
cvHsConPatDetails (RecCon a) = RecCon <$> cvHsRecFieldsPat a
cvHsConPatDetails (InfixCon a b) = InfixCon <$> cvPat a <*> cvPat b

cvHsRecFields
  :: TypeConstraints p q
  => (thing -> Conv thing')
  -> HsRecFields p thing
  -> Conv (HsRecFields q thing')
cvHsRecFields f (HsRecFields a b) =
  HsRecFields <$> traverse (traverse (cvHsRecField' cvFieldOcc f)) a <*> pure b

cvHsRecField'
  :: (id -> Conv id')
  -> (thing -> Conv thing')
  -> HsRecField' id thing
  -> Conv (HsRecField' id' thing')
cvHsRecField' f g (HsRecField a b c) =
  HsRecField <$> traverse f a <*> g b <*> pure c

cvHsRecFieldsPat
  :: TypeConstraints p q
  => HsRecFields p (LPat p) -> Conv (HsRecFields q (LPat  q))
cvHsRecFieldsPat = cvHsRecFields cvPat

cvHsRecUpdField
  :: TypeConstraints p q => HsRecUpdField p -> Conv (HsRecUpdField  q)
cvHsRecUpdField = cvHsRecField' cvAFieldOcc cvLHsExpr

cvRecordBinds
  :: TypeConstraints p q => HsRecordBinds p -> Conv (HsRecordBinds  q)
cvRecordBinds = cvHsRecFields cvLHsExpr

cvFieldOcc :: TypeConstraints p q => FieldOcc p -> Conv (FieldOcc  q)
cvFieldOcc (FieldOcc a b) = FieldOcc a <$> convertName b
cvFieldOcc (XFieldOcc a) = pure (XFieldOcc a)

cvStmtLR
  :: ( TypeConstraints p q
     , XLastStmt p p a ~ XLastStmt q q b
     , XBindStmt p p a ~ XBindStmt q q b
     , XBodyStmt p p a ~ XBodyStmt q q b
     , XApplicativeStmt p p a ~ XApplicativeStmt q q b
     , XLetStmt p p a ~ XLetStmt q q b
     , XRecStmt p p a ~ XRecStmt q q b
     , XParStmt p p a ~ XParStmt q q b
     , XTransStmt p p a ~ XTransStmt q q b
     , XXStmtLR p p a ~ XXStmtLR q q b
     )
  => (a -> Conv b) -> StmtLR p p a -> Conv (StmtLR q q b)
cvStmtLR k (LastStmt a b c d) = LastStmt a
  <$> k b <*> pure c <*> cvSyntaxExpr d
cvStmtLR k (BindStmt a b c d e) = BindStmt a
  <$> cvPat b <*> k c
  <*> cvSyntaxExpr d <*> cvSyntaxExpr e
cvStmtLR k (BodyStmt a b c d) = BodyStmt a
  <$> k b <*> cvSyntaxExpr c
  <*> cvSyntaxExpr d
cvStmtLR _ (ApplicativeStmt a b c) = ApplicativeStmt a
  <$> traverse
        (\(se, aa) -> (,) <$> cvSyntaxExpr se <*> cvApplicativeArg aa)
        b
  <*> traverse cvSyntaxExpr c
cvStmtLR _ (LetStmt a b) = LetStmt a <$> traverse cvHsLocalBinds b
cvStmtLR k (RecStmt a b c d e f g) = RecStmt a
  <$> traverse (traverse (cvStmtLR k)) b
  <*> convertName c
  <*> convertName d
  <*> cvSyntaxExpr e
  <*> cvSyntaxExpr f
  <*> cvSyntaxExpr g
cvStmtLR _ (ParStmt a b c d) = ParStmt a
  <$> traverse cvParStmtBlock b
  <*> cvHsExpr c
  <*> cvSyntaxExpr d
cvStmtLR _ (TransStmt a b c d e f g h i) = TransStmt a b
  <$> traverse (traverse (cvStmtLR cvLHsExpr)) c
  <*> traverse (\(x, y) -> (,) <$> convertName x <*> convertName y) d
  <*> cvLHsExpr e
  <*> traverse cvLHsExpr f
  <*> cvSyntaxExpr g
  <*> cvSyntaxExpr h
  <*> cvHsExpr i
cvStmtLR _ (XStmtLR a) = pure (XStmtLR a)

cvParStmtBlock
  :: TypeConstraints p q => ParStmtBlock p p -> Conv (ParStmtBlock q  q)
cvParStmtBlock (ParStmtBlock a b c d) = ParStmtBlock a
  <$> traverse (traverse (cvStmtLR cvLHsExpr)) b
  <*> convertName c
  <*> cvSyntaxExpr d
cvParStmtBlock (XParStmtBlock a) = pure (XParStmtBlock a)

cvSyntaxExpr :: TypeConstraints p q => SyntaxExpr p -> Conv (SyntaxExpr  q)
cvSyntaxExpr (SyntaxExpr a b c) =
  SyntaxExpr <$> cvHsExpr a <*> pure b <*> pure c

cvHsIPBinds
  :: TypeConstraints p q => HsIPBinds p -> Conv (HsIPBinds  q)
cvHsIPBinds (IPBinds a b) = IPBinds a <$> traverse (traverse cvIPBind) b
cvHsIPBinds (XHsIPBinds a) = pure (XHsIPBinds a)

cvIPBind
  :: TypeConstraints p q => IPBind p -> Conv (IPBind  q)
cvIPBind (IPBind a b c) = IPBind a <$> convertName b <*> cvLHsExpr c
cvIPBind (XIPBind a) = pure (XIPBind a)

cvHsBindLR
  :: TypeConstraints p q => HsBindLR p p -> Conv (HsBindLR q  q)
cvHsBindLR (FunBind a b c d e) = FunBind a
  <$> convertName b
  <*> cvMatchGroup cvLHsExpr c
  <*> pure d <*> pure e
cvHsBindLR (PatBind a b c d ) = PatBind a
  <$> cvPat b <*> cvGRHSs cvLHsExpr c <*> pure d
cvHsBindLR (VarBind a b c d) = VarBind a
  <$> convertName b <*> cvLHsExpr c <*> pure d
cvHsBindLR (PatSynBind a b) = PatSynBind a <$> cvPatSynBind b
cvHsBindLR (AbsBinds {}) =
  unsupported "AbsBind" "HsBindLR" (error "<not printable>")
cvHsBindLR (XHsBindsLR a) = pure (XHsBindsLR a)

cvHsWildCardBndrs
  :: ( TypeConstraints p q, XHsWC p thing ~ XHsWC q thing'
     , XXHsWildCardBndrs p thing ~ XXHsWildCardBndrs q thing'
     )
  => (thing -> Conv thing')
  -> HsWildCardBndrs p thing
  -> Conv (HsWildCardBndrs q thing')
cvHsWildCardBndrs thingF (HsWC a b) = HsWC a <$> thingF b
cvHsWildCardBndrs _ (XHsWildCardBndrs a) = pure (XHsWildCardBndrs a)

cvLHsWcType
  :: TypeConstraints p q => LHsWcType p -> Conv (LHsWcType  q)
cvLHsWcType = cvHsWildCardBndrs (traverse cvType)

cvHsSigWcType
  :: TypeConstraints p q => LHsSigWcType p -> Conv (LHsSigWcType  q)
cvHsSigWcType = cvHsWildCardBndrs (cvHsImplicitBndrs (traverse cvType))

cvHsImplicitBndrs
  :: ( TypeConstraints p q, XHsIB p thing ~ XHsIB q thing'
     , XXHsImplicitBndrs p thing ~ XXHsImplicitBndrs q thing'
     )
  => (thing -> Conv thing')
  -> HsImplicitBndrs p thing
  -> Conv (HsImplicitBndrs q thing')
cvHsImplicitBndrs f (HsIB a b) = HsIB a <$> f b
cvHsImplicitBndrs _ (XHsImplicitBndrs a) = pure (XHsImplicitBndrs a)

cvType :: TypeConstraints p q => HsType p -> Conv (HsType  q)
cvType (HsForAllTy a b c) = HsForAllTy a
  <$> traverse (traverse cvHsTyVarBndr) b
  <*> traverse cvType c
cvType (HsQualTy a b c) = HsQualTy a
  <$> traverse (traverse (traverse cvType)) b
  <*> traverse cvType c
cvType (HsTyVar a b c) = HsTyVar a b <$> convertName c
cvType (HsAppTy a b c) = HsAppTy a
  <$> traverse cvType b
  <*> traverse cvType c
cvType (HsAppKindTy a b c) = HsAppKindTy a
  <$> traverse cvType b
  <*> traverse cvType c
cvType (HsFunTy a b c) = HsFunTy a
  <$> traverse cvType b
  <*> traverse cvType c
cvType (HsListTy a b) = HsListTy a <$> traverse cvType b
cvType (HsTupleTy a b c) = HsTupleTy a b <$> traverse (traverse cvType) c
cvType (HsSumTy a b) = HsSumTy a <$> traverse (traverse cvType) b
cvType (HsOpTy a b c d) = HsOpTy a
  <$> traverse cvType b
  <*> convertName c
  <*> traverse cvType d
cvType (HsParTy a b) = HsParTy a <$> traverse cvType b
cvType (HsIParamTy a b c) = HsIParamTy a b <$> traverse cvType c
cvType (HsKindSig a b c) = HsKindSig a
  <$> traverse cvType b
  <*> traverse cvType c
cvType (HsBangTy a b c) = HsBangTy a b <$> traverse cvType c
cvType (HsRecTy a b) = HsRecTy a <$> traverse (traverse cvConDeclField) b
cvType (HsExplicitListTy a b c) = HsExplicitListTy a b
  <$> traverse (traverse cvType) c
cvType (HsExplicitTupleTy a b) = HsExplicitTupleTy a
  <$> traverse (traverse cvType) b
cvType (HsTyLit a b) = pure (HsTyLit a b)
cvType (HsWildCardTy a) = pure (HsWildCardTy a)
cvType (HsDocTy a b c) = HsDocTy a <$> traverse cvType b <*> pure c
cvType (HsSpliceTy a b) = HsSpliceTy a <$> cvHsSplice b
cvType (HsStarTy a b) = pure (HsStarTy a b)
cvType (XHsType a) = pure (XHsType a)

cvHsTyVarBndr
  :: TypeConstraints p q => HsTyVarBndr p -> Conv (HsTyVarBndr  q)
cvHsTyVarBndr (UserTyVar a b) = UserTyVar a <$> convertName b
cvHsTyVarBndr (KindedTyVar a b c) = KindedTyVar a
  <$> convertName b
  <*> traverse cvType c
cvHsTyVarBndr (XTyVarBndr a) = pure (XTyVarBndr a)

cvApplicativeArg
  :: TypeConstraints p q => ApplicativeArg p -> Conv (ApplicativeArg  q)
cvApplicativeArg (ApplicativeArgOne a b c d) = ApplicativeArgOne a
  <$> cvPat b <*> cvLHsExpr c <*> pure d
cvApplicativeArg (ApplicativeArgMany a b c d) = ApplicativeArgMany a
  <$> traverse (traverse (cvStmtLR cvLHsExpr)) b <*> cvHsExpr c
  <*> cvPat d
cvApplicativeArg (XApplicativeArg a) = pure (XApplicativeArg a)

cvSig :: TypeConstraints p q => Sig p -> Conv (Sig  q)
cvSig (TypeSig a b c) = TypeSig a <$> convertName b <*> cvHsSigWcType c
cvSig (PatSynSig a b c) = PatSynSig a
  <$> convertName b <*> cvHsImplicitBndrs (traverse cvType) c
cvSig (ClassOpSig a b c d) = ClassOpSig a b
  <$> convertName c <*> cvHsImplicitBndrs (traverse cvType) d
cvSig (InlineSig a b c) = InlineSig a <$> convertName b <*> pure c
cvSig (FixSig a b) = FixSig a <$> cvFixitySig b
cvSig (SpecSig a b c d) = SpecSig a
  <$> convertName b
  <*> traverse (cvHsImplicitBndrs (traverse cvType)) c
  <*> pure d
cvSig (SpecInstSig a b c) = SpecInstSig a b
  <$> cvHsImplicitBndrs (traverse cvType) c
cvSig (SCCFunSig a b c d) = SCCFunSig a b <$> convertName c <*> pure d
cvSig (CompleteMatchSig a b c d) = CompleteMatchSig a b
  <$> convertName c <*> convertName d
cvSig (MinimalSig a b c) = MinimalSig a b <$> traverse (traverse convertName) c
cvSig (IdSig {}) = unsupported "IdSig" "Sig" (error "<not printable>")
cvSig (XSig a) = pure (XSig a)

cvFixitySig :: TypeConstraints p q => FixitySig p -> Conv (FixitySig  q)
cvFixitySig (FixitySig a b c) = FixitySig a <$> convertName b <*> pure c
cvFixitySig (XFixitySig a) = pure (XFixitySig a)

cvPatSynBind :: TypeConstraints p q => PatSynBind p p -> Conv (PatSynBind q  q)
cvPatSynBind (PSB a b c d e) = PSB a
  <$> convertName b
  <*> cvHsPatSynDetails convertName c <*> cvPat d
  <*> cvHsPatSynDir e
cvPatSynBind (XPatSynBind a) = pure (XPatSynBind a)

cvHsPatSynDetails
  :: (a -> Conv b)
  -> HsPatSynDetails a
  -> Conv (HsPatSynDetails b)
cvHsPatSynDetails f = cvHsConDetails f (traverse (cvRecordPatSynField f))

cvRecordPatSynField
  :: (a -> Conv b)
  -> RecordPatSynField a
  -> Conv (RecordPatSynField b)
cvRecordPatSynField f (RecordPatSynField a b) =
  RecordPatSynField <$> f a <*> f b

cvHsPatSynDir :: TypeConstraints p q => HsPatSynDir p -> Conv (HsPatSynDir  q)
cvHsPatSynDir Unidirectional = pure Unidirectional
cvHsPatSynDir ImplicitBidirectional = pure ImplicitBidirectional
cvHsPatSynDir (ExplicitBidirectional a) = ExplicitBidirectional
  <$> cvMatchGroup cvLHsExpr a

-- * Looking up modules/packages for Orig names

-- this rejects wired in packages, because we want to leave them untouched
parseUnitId' :: String -> Maybe (String, String, Maybe String)
parseUnitId' = parse

  where
    parse s = case splitOn '-' (reverse s) of
      ("":_) -> Nothing
      xs | length xs >= 1 && last xs == "" -> Nothing
      (hash:ver:name) | isVersion ver ->
         Just (intercalate "-" (reverse name), ver, Just hash)
      (ver:name) | isVersion ver ->
         Just (intercalate "-" (reverse name), ver, Nothing)
      _ -> Nothing
    splitOn c = go []
      where go acc (x:xs)
              | x == c    = acc : go "" xs
              | otherwise = go (x:acc) xs
            go acc [] = [acc]
    isVersion = go False
      -- True: waiting for digit or dot (we've seen a digit last)
      -- False: waiting for digit (we've just seen a dot)
      where go False (c:cs)
              | isDigit c = go True cs
              | otherwise = False
            go True (c:cs)
              | isDigit c = go True cs
              | c == '.'  = go False cs
              | otherwise = False
            go b [] = b -- if we've seen a dot last (False), we fail
                        -- otherwise, the version number can end here

-- | Look up the module from the same package, but built by the
--   current compiler, therefore with a slightly different hash
--   in the unit id than the input Module, which was built by some
--   non-cross-compiling GHC.
findEquivalentModule :: Module -> RnM (Maybe Module)
findEquivalentModule mod = do
  liftIO $ putStrLn ("Looking for equivalent to: " ++ unitIdStr)
  case parseUnitId' unitIdStr of
    Nothing -> return Nothing
    Just (pkg, ver, _mhash) -> do
      muid <- lookFor pkg ver
      maybe (pure Nothing) (\uid -> return $ Just (mod { moduleUnitId = uid })) muid

  where unitIdStr = unitIdString (moduleUnitId mod)

lookFor :: String -> String -> RnM (Maybe UnitId)
lookFor pkg ver = do
  dflags <- getDynFlags
  let pkgid = mkFastString (pkg ++ "-" ++ ver)
      pkgs = searchPackageId dflags (SourcePackageId pkgid)
  liftIO $ putStrLn ("Looking for: " ++ pkg ++ "-" ++ ver)
  liftIO . putStrLn . unwords $
    [ "Found", show (length pkgs), "pkgs:" ] ++
    [ unitIdString (packageConfigId p) | p <- pkgs ]
  if null pkgs then pure Nothing else pure (Just $ packageConfigId (head pkgs))
