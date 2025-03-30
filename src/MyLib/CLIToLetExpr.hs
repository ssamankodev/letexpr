{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module MyLib.CLIToLetExpr(linearReferenceLetExprParse, mutualReferenceLetExprParse) where

  import Data.Text (Text)
  import MyLib.LetExpr

  data Tokens
    = Let
    | Rec
    | Raw
    | LetRaw
    | LetRec
    | Equals
    | In
    | NonKeyWord Text

  data MultiTokens
    = MLet
    | MRec
    | MRaw
    | MEquals
    | MIn
    | MComma
    | MNonKeyWord Text

  tokenize :: [Text] -> [Tokens]
  tokenize [] = []
  tokenize (chunk:rest)
    | chunk == "let" = case rest of
        [] -> [Let]
        [_] -> Let              : tokenize rest
        newChunk:newRest ->
          if newChunk == "rec"
          then         LetRec           : tokenize newRest
          else if newChunk == "raw"
          then         LetRaw           : tokenize newRest
          else         Let              : tokenize rest
    | chunk == "rec" = Rec              : tokenize rest
    | chunk == "raw" = Raw              : tokenize rest
    | chunk == "="   = Equals           : tokenize rest
    | chunk == "in"  = In               : tokenize rest
    | otherwise      = NonKeyWord chunk : tokenize rest

  inverseTokenize :: [Tokens] -> [Text]
  inverseTokenize [] = []
  inverseTokenize (Let:rest) = "let" : inverseTokenize rest
  inverseTokenize (Rec:rest) = "rec" : inverseTokenize rest
  inverseTokenize (Raw:rest) = "raw" : inverseTokenize rest
  inverseTokenize (LetRaw:rest) = "let" : "raw" : inverseTokenize rest
  inverseTokenize (LetRec:rest) = "let" : "rec" : inverseTokenize rest
  inverseTokenize (Equals:rest) = "=" : inverseTokenize rest
  inverseTokenize (In:rest) = "in" : inverseTokenize rest
  inverseTokenize (NonKeyWord chunk:rest) = chunk : inverseTokenize rest

  multiTokenize :: [Text] -> [MultiTokens]
  multiTokenize [] = []
  multiTokenize (chunk:rest)
    | chunk == "let" = MLet              : multiTokenize rest
    | chunk == "rec" = MRec              : multiTokenize rest
    | chunk == "raw" = MRaw              : multiTokenize rest
    | chunk == "="   = MEquals           : multiTokenize rest
    | chunk == "in"  = MIn               : multiTokenize rest
    | chunk == ","   = MComma            : multiTokenize rest
    | otherwise      = MNonKeyWord chunk : multiTokenize rest

  letBindingTextVar
    :: Text
    -> (a -> LetBinding a)
  letBindingTextVar text = letBinding (toVar text)

  recLet :: LetBinding a -> LetBinding (Either (RecursionAllowance, a) b)
  recLet = fmap (Left . (Permit,))

  regLet :: LetBinding a -> LetBinding (Either (RecursionAllowance, a) b)
  regLet = fmap (Left . (Prohibit,))

  rawLet :: LetBinding Text -> LetBinding (Either a Text)
  rawLet = fmap Right

  linearReferenceLetExprParse :: [Text] -> Maybe (LetExpr (Either (RecursionAllowance, Text) Text) Text)
  linearReferenceLetExprParse = linearReferenceLetExprTokens . tokenize

  linearReferenceLetExprTokens :: [Tokens] -> Maybe (LetExpr (Either (RecursionAllowance, Text) Text) Text)
  linearReferenceLetExprTokens (Let : NonKeyWord var : Equals : NonKeyWord body : In : NonKeyWord finalExpression : []) =
    Just $ letExprLetBindFinal (regLet $ letBindingTextVar var body) finalExpression
  linearReferenceLetExprTokens (LetRec : NonKeyWord var : Equals : NonKeyWord body : In : NonKeyWord finalExpression : []) =
    Just $ letExprLetBindFinal (recLet $ letBindingTextVar var body) finalExpression
  linearReferenceLetExprTokens (LetRaw : NonKeyWord var : Equals : NonKeyWord body : In : NonKeyWord finalExpression : []) =
    Just $ letExprLetBindFinal (rawLet $ letBindingTextVar var body) finalExpression
  linearReferenceLetExprTokens (LetRec : NonKeyWord var : Equals : NonKeyWord body : In : rest) =
    letExprLetBind (recLet $ letBindingTextVar var body) <$> linearReferenceLetExprTokens rest
  linearReferenceLetExprTokens (Let : NonKeyWord var : Equals : NonKeyWord body : In : rest) =
    letExprLetBind (regLet $ letBindingTextVar var body) <$> linearReferenceLetExprTokens rest
  linearReferenceLetExprTokens (LetRaw : NonKeyWord var : Equals : NonKeyWord body : In : rest) =
    letExprLetBind (rawLet $ letBindingTextVar var body) <$> linearReferenceLetExprTokens rest
  linearReferenceLetExprTokens _ = Nothing

  mutualReferenceLetExprParse :: [Text] -> Maybe (LetExpr (Either (RecursionAllowance, Text) Text) Text)
  mutualReferenceLetExprParse chunks = case multiTokenize chunks of
    (MLet : rest) -> mutualReferenceLetExprMultiTokens rest
    _ -> Nothing

  mutualReferenceLetExprMultiTokens :: [MultiTokens] -> Maybe (LetExpr (Either (RecursionAllowance, Text) Text) Text)
  mutualReferenceLetExprMultiTokens (MRaw : MNonKeyWord var : MEquals : MNonKeyWord body : MIn : MNonKeyWord finalExpression : []) =
    Just $ letExprLetBindFinal (rawLet $ letBindingTextVar var body) finalExpression
  mutualReferenceLetExprMultiTokens (MRec : MNonKeyWord var : MEquals : MNonKeyWord body : MIn : MNonKeyWord finalExpression : []) =
    Just $ letExprLetBindFinal (recLet $ letBindingTextVar var body) finalExpression
  mutualReferenceLetExprMultiTokens (MNonKeyWord var : MEquals : MNonKeyWord body : MIn : MNonKeyWord finalExpression : []) =
    Just $ letExprLetBindFinal (regLet $ letBindingTextVar var body) finalExpression
  mutualReferenceLetExprMultiTokens (MRec : MNonKeyWord var : MEquals : MNonKeyWord body : MComma : rest) =
    letExprLetBind (recLet $ letBindingTextVar var body) <$> mutualReferenceLetExprMultiTokens rest
  mutualReferenceLetExprMultiTokens (MNonKeyWord var : MEquals : MNonKeyWord body : MComma : rest) =
    letExprLetBind (regLet $ letBindingTextVar var body) <$> mutualReferenceLetExprMultiTokens rest
  mutualReferenceLetExprMultiTokens (MRaw : MNonKeyWord var : MEquals : MNonKeyWord body : MComma : rest) =
    letExprLetBind (rawLet $ letBindingTextVar var body) <$> mutualReferenceLetExprMultiTokens rest
  mutualReferenceLetExprMultiTokens _ = Nothing
