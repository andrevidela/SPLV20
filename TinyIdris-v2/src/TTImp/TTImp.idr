module TTImp.TTImp

import Core.TT

import Deriving.Show

%hide Reflection.TT.Name

%language ElabReflection

public export
data RawImp : Type where
     IVar : Name -> RawImp
     IPi : PiInfo -> Maybe Name ->
           (argTy : RawImp) -> (retTy : RawImp) -> RawImp
     ILam : PiInfo -> Maybe Name ->
            (argTy : RawImp) -> (scope : RawImp) -> RawImp
     IPatvar : Name -> (ty : RawImp) -> (scope : RawImp) -> RawImp
        -- ^ Idris doesn't need this since the pattern variable names are
        -- inferred, but in this initial version everything is explicit
     IApp : RawImp -> RawImp -> RawImp

     Implicit : RawImp
     IType : RawImp

%hint export
impRawImp : Show RawImp
impRawImp = %runElab derive

public export
data ImpTy : Type where
     MkImpTy : (n : Name) -> (ty : RawImp) -> ImpTy

%hint export
impTy : Show ImpTy
impTy = %runElab derive

public export
data ImpClause : Type where
     PatClause : (lhs : RawImp) -> (rhs : RawImp) -> ImpClause
%hint export
impClause : Show ImpClause
impClause = %runElab derive

public export
data ImpData : Type where
     MkImpData : (n : Name) ->
                 (tycon : RawImp) -> -- type constructor type
                 (datacons : List ImpTy) -> -- constructor type declarations
                 ImpData
%hint export
impData : Show ImpData
impData = %runElab derive

public export
data ImpDecl : Type where
     IClaim : ImpTy -> ImpDecl
     IData : ImpData -> ImpDecl
     IDef : Name -> List ImpClause -> ImpDecl

%hint export
impShow : Show ImpDecl
impShow = %runElab derive

export
apply : RawImp -> List RawImp -> RawImp
apply f [] = f
apply f (x :: xs) = apply (IApp f x) xs

export
getFn : RawImp -> RawImp
getFn (IApp f arg) = getFn f
getFn f = f
