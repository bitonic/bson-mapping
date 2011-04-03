{-# Language TemplateHaskell #-}

{- |

This module aims to make mapping between algebraic data types and bson
documents easy.

The rules: the data type must have one constructor, and named
fields. All the fields must be instances of 'Val'.

You can also generate documents with 'selectFields', which takes a
list of functions names that of type a -> b and returns a function
of type a -> Document.

Example:

> {-# Language TemplateHaskell #-}
>
> import Data.Bson.Mapping
> import Data.Time.Clock
>
> data Post = Post { time :: UTCTime
>                  , author :: String
>                  , content :: String 
>                  , votes :: Int
>                  }
>           deriving (Show, Read, Eq, Ord)
> $(deriveBson ''Post)
>
> main :: IO ()
> main = do
>   now <- getCurrentTime
>   let post = Post now "francesco" "lorem ipsum" 5
>   (fromBson (toBson post) :: IO Post) >>= print
>   print $ toBson post
>   print $ $(selectFields ['time, 'content]) post

-}

module Data.Bson.Mapping (
    Bson (..)
  , deriveBson  
  , selectFields
  ) where

import qualified Data.Bson as B
import Language.Haskell.TH
import Language.Haskell.TH.Lift ()

class Bson a where
  toBson   :: a -> B.Document
  fromBson :: Monad m => B.Document -> m a


deriveBson :: Name -> Q [Dec]
deriveBson type' = do
  (cx, con, keys) <- bsonType
  (constr, fields) <- parseCon con
  let context = [ classP ''B.Val [varT key] | key <- keys ] ++ map return cx
  i <- instanceD (sequence context) (mkType ''Bson [mkType type' (map varT keys)])
       [ funD 'toBson [clause [] (normalB $ selectFields fields) []]
       , deriveFromBson fields constr
       ]
  return [i]

  where

    bsonType = do
      info <- reify type'
      case info of
        TyConI (DataD cx _ keys [con] _)  -> return (cx, con, map conv keys)
        TyConI (NewtypeD cx _ keys con _) -> return (cx, con, map conv keys)
        _ -> inputError
    
    parseCon con = do
      case con of
        RecC name fields -> return (name, map (\(n, _, _) -> n) fields)
        _             -> inputError
    
    mkType con = foldl appT (conT con)
    
    conv (PlainTV nm)    = nm
    conv (KindedTV nm _) = nm
    
    inputError = error "deriveBson: Invalid type provided. The type must be a data with a single constructor or a newtype. The constructor must have named fields."
                 
    deriveFromBson fields constr = do
      doc <- newName "doc"
      (fields', stmts) <- genStmts fields doc
      let ci = noBindS $ [| return $(recConE constr fields') |]
      funD 'fromBson [clause [varP doc] (normalB $ doE (stmts ++ [ci])) []]
      
    genStmts [] _ = return ([], [])
    genStmts (f : fs) doc = do
      fvar <- newName "f"
      let stmt = bindS (varP fvar) $ [| B.lookup (B.u (nameBase f)) $(varE doc) |]
      (fields, stmts) <- genStmts fs doc
      return $ (return (f, VarE fvar) : fields, stmt : stmts)
    
selectFields :: [Name] -> Q Exp
selectFields ns = do
  d <- newName "d"
  e <- gf d ns
  lamE [varP d] (return e)
  where
    gf _ []        = [| [] |]
    gf d (n : ns') = [| (B.u (nameBase n) B.=: $(varE n) $(varE d)) : $(gf d ns') |]