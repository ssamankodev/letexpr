{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
        newChunk:[] -> Let              : tokenize rest
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

  linearReferenceLetExprParse :: [Text] -> Maybe (LetExpr (Either (RecursionAllowance, ExprText) ExprText) ExprText)
  linearReferenceLetExprParse = linearReferenceLetExprTokens . tokenize

  linearReferenceLetExprTokens :: [Tokens] -> Maybe (LetExpr (Either (RecursionAllowance, ExprText) ExprText) ExprText)
  linearReferenceLetExprTokens (Let : NonKeyWord var : Equals : NonKeyWord body : In : NonKeyWord finalExpression : []) =
    Just $ LetBindFinal (LetBinding (toVar var) (Left (Prohibit, ExprText body))) (ExprText finalExpression)
  linearReferenceLetExprTokens (LetRec : NonKeyWord var : Equals : NonKeyWord body : In : NonKeyWord finalExpression : []) =
    Just $ LetBindFinal (LetBinding (toVar var) (Left (Permit, ExprText body))) (ExprText finalExpression)
  linearReferenceLetExprTokens (LetRaw : NonKeyWord var : Equals : NonKeyWord body : In : NonKeyWord finalExpression : []) =
    Just $ LetBindFinal (LetBinding (toVar var) (Right (ExprText body))) (ExprText finalExpression)
  linearReferenceLetExprTokens (LetRec : NonKeyWord var : Equals : NonKeyWord body : In : rest) =
    fmap (LetBind (LetBinding (toVar var) (Left (Permit, ExprText body)))) $ linearReferenceLetExprTokens rest
  linearReferenceLetExprTokens (Let : NonKeyWord var : Equals : NonKeyWord body : In : rest) =
    fmap (LetBind (LetBinding (toVar var) (Left (Prohibit, ExprText body)))) $ linearReferenceLetExprTokens rest
  linearReferenceLetExprTokens (LetRaw : NonKeyWord var : Equals : NonKeyWord body : In : rest) =
    fmap (LetBind (LetBinding (toVar var) (Right (ExprText body)))) $ linearReferenceLetExprTokens rest
  linearReferenceLetExprTokens _ = Nothing

  mutualReferenceLetExprParse :: [Text] -> Maybe (LetExpr (Either (RecursionAllowance, ExprText) ExprText) ExprText)
  mutualReferenceLetExprParse chunks = case multiTokenize chunks of
    (MLet : rest) -> mutualReferenceLetExprMultiTokens rest
    _ -> Nothing

  mutualReferenceLetExprMultiTokens :: [MultiTokens] -> Maybe (LetExpr (Either (RecursionAllowance, ExprText) ExprText) ExprText)
  mutualReferenceLetExprMultiTokens (MRec : MNonKeyWord var : MEquals : MNonKeyWord body : MIn : MNonKeyWord finalExpression : []) =
    Just $ LetBindFinal (LetBinding (toVar var) (Left (Permit, ExprText body))) (ExprText finalExpression)
  mutualReferenceLetExprMultiTokens (MRaw : MNonKeyWord var : MEquals : MNonKeyWord body : MIn : MNonKeyWord finalExpression : []) =
    Just $ LetBindFinal (LetBinding (toVar var) (Right (ExprText body))) (ExprText finalExpression)
  mutualReferenceLetExprMultiTokens (MNonKeyWord var : MEquals : MNonKeyWord body : MIn : MNonKeyWord finalExpression : []) =
    Just $ LetBindFinal (LetBinding (toVar var) (Left (Prohibit, ExprText body))) (ExprText finalExpression)
  mutualReferenceLetExprMultiTokens (MRec : MNonKeyWord var : MEquals : MNonKeyWord body : MComma : rest) =
    fmap (LetBind (LetBinding (toVar var) (Left (Permit, ExprText body)))) $ mutualReferenceLetExprMultiTokens rest
  mutualReferenceLetExprMultiTokens (MRaw : MNonKeyWord var : MEquals : MNonKeyWord body : MComma : rest) =
    fmap (LetBind (LetBinding (toVar var) (Right (ExprText body)))) $ mutualReferenceLetExprMultiTokens rest
  mutualReferenceLetExprMultiTokens (MNonKeyWord var : MEquals : MNonKeyWord body : MComma : rest) =
    fmap (LetBind (LetBinding (toVar var) (Left (Prohibit, ExprText body)))) $ mutualReferenceLetExprMultiTokens rest
  mutualReferenceLetExprMultiTokens _ = Nothing
