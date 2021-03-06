# -----------------------------------------------------------------------------
#
# (c) 2009 The University of Glasgow
#
# This file is part of the GHC build system.
#
# To understand how the build system works and how to modify it, see
#      https://gitlab.haskell.org/ghc/ghc/wikis/building/architecture
#      https://gitlab.haskell.org/ghc/ghc/wikis/building/modifying
#
# -----------------------------------------------------------------------------

utils/genapply_USES_CABAL           = YES
utils/genapply_PACKAGE              = genapply
utils/genapply_dist_PROGNAME        = genapply
utils/genapply_dist_INSTALL         = NO
utils/genapply_dist_INSTALL_INPLACE = YES

ifeq "$(GhcUnregisterised)" "YES"
utils/genapply_CONFIGURE_OPTS = --flag unregisterised
endif

$(eval $(call build-prog,utils/genapply,dist,0))
