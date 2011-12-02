{-# Language TemplateHaskell #-}

{- |

This module aims to make mapping between algebraic data types and bson
documents easy.

You can also generate documents with 'selectFields', which takes a
list of functions names that of type a -> b and returns a function
of type a -> Document.

Example:

> import Data.Bson.Mapping
> import Data.Time.Clock
> import Data.Data (Data, Typeable)
>
> data Post = Post { time :: UTCTime
>                  , author :: String
>                  , content :: String 
>                  , votes :: Int
>                  }
>           deriving (Show, Read, Eq, Ord, Data, Typeable)
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

module Data.Bson.Mapping
       ( Bson (..)
       , deriveBson  
       , selectFields
       , getLabel
       , getConsDoc
       , subDocument
       , getField
       ) where

import Prelude hiding (lookup)

import Data.Bson
import Data.Data               (Data, Typeable)
import Data.CompactString.UTF8 (append, cons)

import Language.Haskell.TH
import Language.Haskell.TH.Lift ()

class (Show a, Eq a, Data a, Typeable a) => Bson a where
  toBson     :: a -> Document
  fromBson   :: Monad m => Document -> m a

-- | Derive 'Bson' and 'Val' declarations for a data type.
deriveBson :: Name -> Q [Dec]
deriveBson type' = do
  (cx, conss, keys) <- bsonType
  
  -- Each type in the data type must be an instance of val
  let context = [ classP ''Val [varT key] | key <- keys ] ++ map return cx
  
  -- Generate the functions for the Bson instance
  let fs = [ funD 'toBson (map deriveToBson conss)
           , funD 'fromBson [clause [] (normalB $ deriveFromBson conss) []]
           ]
  i <- instanceD (sequence context) (mkType ''Bson [mkType type' (map varT keys)]) fs

  -- Generate the Val instance (easy, since a Bson doc is
  -- automatically a Val)
  doc <- newName "doc"         
  i' <- instanceD (cxt []) (mkType ''Val [mkType type' (map varT keys)])
        [ funD 'val   [clause [] (normalB $ [| Doc . toBson |]) []]
        , funD 'cast' [ clause [conP 'Doc [varP doc]] (normalB $ [| fromBson $(varE doc) |]) []
                      , clause [[p| _ |]] (normalB $ [| Nothing |]) []
                      ]          
        ]
  
  return [i, i']
  
  where

    -- Check that wha has been provided is a data/newtype declaration
    bsonType = do
      info <- reify type'
      case info of
        TyConI (DataD cx _ keys conss _)  -> return (cx, conss, map conv keys)
        TyConI (NewtypeD cx _ keys con _) -> return (cx, [con], map conv keys)
        _ -> inputError
    
    mkType con = foldl appT (conT con)
    
    conv (PlainTV n)    = n
    conv (KindedTV n _) = n
    
    inputError = error $ "deriveBson: Invalid type provided. " ++
                         "The type must be a data type or a newtype. " ++
                         "Currently infix constructors and existential types are not supported."

    
    -- deriveToBson generates the clauses that pattern match the
    -- constructors of the data type, and then the function to convert
    -- them to Bson.
    deriveToBson :: Con -> Q Clause
    -- If it's a constructor with named fields, we can simply use
    -- selectFields
    deriveToBson (RecC name fields) = do
      let fieldsDoc = selectFields $ map (\(n, _, _) -> n) fields
      consDoc <- getConsDoc name
      i <- newName "i"
      -- With data Foo = Foo {one :: String, two :: Int}
      -- This will produce something like:
      -- toBson i@Foo{} = merge ["_cons" =: "Foo"] ["one" =: one i, "two" =: two i]
      clause [asP i (recP name [])] (normalB $ [| (merge $(getConsDoc name)) ($fieldsDoc $(varE i)) |]) []
    -- If it's a normal constructor, generate a document with an array
    -- with the data.
    deriveToBson (NormalC name types) = do
      -- There are no types, but just a constructor (data Foo = Foo),
      -- simply store the constructor name.
      if null types
        then clause [recP name []] (normalB $ getConsDoc name) []
        -- Else, convert all the data inside the data types to an array
        -- and store it in the document.
        -- Example: if we have 'Foo = Foo String Int', 'Foo "francesco" 4'
        -- will be converted to ["_cons" =: "Foo", "_data" =: ["francesco", 4]]
        else do
          fields <- mapM (\_ -> newName "f") types
          clause [conP name (map varP fields)]
            (normalB $ [| (merge $(getConsDoc name)) . (\f -> [dataField =: f]) $ $(listE (map varE fields)) |]) []
    deriveToBson _ = inputError


    -- deriveFromBson gets the _cons field, and guesses which
    -- constructor to use. Fails if it can't match _cons with a
    -- constructor of the data type.
    deriveFromBson :: [Con] -> Q Exp
    deriveFromBson conss = do
      con <- newName "con"
      docN <- newName "doc"
      (SigE _ (ConT strtype)) <- runQ [| "" :: String |]
      let doc = varE docN
      lamE [varP docN] $ doE
        [ bindS (varP con) [| lookup consField $doc |]
        , noBindS $ caseE (sigE (varE con) (conT strtype)) (map (genMatch doc) conss ++ noMatch)
        ]
 
    noMatch = [match [p| _ |] (normalB [| fail "Couldn't find right constructor" |]) []]


    -- Generate the case statements after we get the _cons field, to
    -- match it and get the right constructor
    genMatch :: Q Exp -> Con -> Q Match
    genMatch doc (RecC name fields) =
      -- Match the string literal that we got from the doc (_cons)
      flip (match (litP $ StringL $ nameBase name)) [] $ do
        (fields', stmts) <- genStmts (map (\(n, _, _) -> n) fields) doc
        let ci = noBindS $ [| return $(recConE name fields') |]
        normalB (doE $ stmts ++ [ci])
    genMatch doc (NormalC name types) =
      flip (match (litP $ StringL $ nameBase name)) [] $
        if null types
        then normalB [| return $(conE name) |]
        else do
          -- In the case of a normal constructor with types in it, we
          -- have to get the _data field and apply it to the
          -- constructor
          -- This gets the data, checks that the length is equal to
          -- the number of types in the data type, then pattern
          -- matches the array that we got and applies it to the
          -- constructor (the foldl).
          data' <- newName "data"
          let typesN = length types
          types' <- mapM (\_ -> newName "t") types
          let typesP = listP $ map varP types'
              con    = foldl (\e f -> (appE e (varE f))) (conE name) types'
          normalB $ doE [ bindS (varP data') [| lookup dataField $doc |]
                        , noBindS [| if length $(varE data') /= $([| typesN |])
                                     then fail "Wrong data for the constructor."
                                     else $(doE [ letS [valD typesP (normalB $ varE data') []]
                                                , noBindS [| return $con |]
                                                ])
                                   |]
                        ]
    genMatch _ _ = inputError

    -- genStmts generates the lookups on the document and also returns
    -- the vars names that are used in the statements, coupled with
    -- the original fields.
    genStmts :: [Name] -> Q Exp -> Q ([Q (Name, Exp)], [Q Stmt])
    genStmts [] _ = return ([], [])
    genStmts (f : fs) doc = do
      fvar <- newName "f"
      let stmt = bindS (varP fvar) $ [| lookup (u (nameBase f)) $doc |]
      (fields, stmts) <- genStmts fs doc
      return $ (return (f, VarE fvar) : fields, stmt : stmts)


dataField, consField :: UString
dataField = u "_data"
consField = u "_cons"

{-|

Select only certain fields in a document, see the code sample at the
top.

Please note that there is no checking for the names to be actual
fields of the bson document mapped to a datatype, so be careful.

-}
selectFields :: [Name] -> Q Exp
selectFields ns = do
  d <- newName "d"
  e <- gf d ns
  lamE [varP d] (return e)
  where
    gf _ []        = [| [] |]
    gf d (n : ns') = [| ($(getLabel n) =: $(varE n) $(varE d)) : $(gf d ns') |]

{-|

Get a document that identifies the data type - @getConsDoc ''Post@.

This is useful to select all documents mapped to a certain data type.

-}
getConsDoc :: Name -> Q Exp
getConsDoc n = [| [consField =: nameBase n] |]

-- | Simple function to select fields in a nested document.
subDocument :: Label -> Document -> Document
subDocument lab doc = [append lab (cons '.' l) := v | (l := v) <- doc]

getLabel :: Name -> Q Exp
getLabel n = [| u (nameBase n) |]

{-|

Returns a function that gets a datatype and a value, and generates a 'Document' consisting of one field - the label provided - and the value of that datatype.

@$(getField 'time) post@ will generate @[\"time\" =: time post]@.

-}
getField :: Name -> Q Exp
getField n = [| \d -> $(getLabel n) =: $(varE n) d |]