{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module MyLib.CLIToLetExpr(linearReferenceLetExprParse, mutualReferenceLetExprParse) where

  import Data.Text (Text)
  import Data.Text.Encoding as TE
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
  letBindingTextVar text = letBinding (bsToVar $ TE.encodeUtf8 text)

  linearReferenceLetExprParse :: [Text] -> Maybe (LetExpr (Either (RecursionAllowance, Text) Text) Text)
  linearReferenceLetExprParse = linearReferenceLetExprTokens . tokenize

  linearReferenceLetExprTokens :: [Tokens] -> Maybe (LetExpr (Either (RecursionAllowance, Text) Text) Text)
  linearReferenceLetExprTokens [Let, NonKeyWord var , Equals, NonKeyWord body, In, NonKeyWord finalExpression] =
    Just $ letExprLetBindFinal (letBindingTextVar var (Left (Prohibit, body))) finalExpression
  linearReferenceLetExprTokens [LetRec, NonKeyWord var, Equals, NonKeyWord body, In, NonKeyWord finalExpression] =
    Just $ letExprLetBindFinal (letBindingTextVar var (Left (Permit, body))) finalExpression
  linearReferenceLetExprTokens [LetRaw, NonKeyWord var, Equals, NonKeyWord body, In, NonKeyWord finalExpression] =
    Just $ letExprLetBindFinal (letBindingTextVar var (Right body)) finalExpression
  linearReferenceLetExprTokens (LetRec : NonKeyWord var : Equals : NonKeyWord body : In : rest) =
    letExprLetBind (letBindingTextVar var (Left (Permit, body))) <$> linearReferenceLetExprTokens rest
  linearReferenceLetExprTokens (Let : NonKeyWord var : Equals : NonKeyWord body : In : rest) =
    letExprLetBind (letBindingTextVar var (Left (Prohibit, body))) <$> linearReferenceLetExprTokens rest
  linearReferenceLetExprTokens (LetRaw : NonKeyWord var : Equals : NonKeyWord body : In : rest) =
    letExprLetBind (letBindingTextVar var (Right body)) <$> linearReferenceLetExprTokens rest
  linearReferenceLetExprTokens _ = Nothing

  mutualReferenceLetExprParse :: [Text] -> Maybe (LetExpr (Either (RecursionAllowance, Text) Text) Text)
  mutualReferenceLetExprParse chunks = case multiTokenize chunks of
    (MLet : rest) -> mutualReferenceLetExprMultiTokens rest
    _ -> Nothing

  mutualReferenceLetExprMultiTokens :: [MultiTokens] -> Maybe (LetExpr (Either (RecursionAllowance, Text) Text) Text)
  mutualReferenceLetExprMultiTokens [MRaw, MNonKeyWord var, MEquals, MNonKeyWord body, MIn, MNonKeyWord finalExpression] =
    Just $ letExprLetBindFinal (letBindingTextVar var (Right body)) finalExpression
  mutualReferenceLetExprMultiTokens [MRec, MNonKeyWord var, MEquals, MNonKeyWord body, MIn, MNonKeyWord finalExpression] =
    Just $ letExprLetBindFinal (letBindingTextVar var (Left (Permit, body))) finalExpression
  mutualReferenceLetExprMultiTokens [MNonKeyWord var, MEquals, MNonKeyWord body, MIn, MNonKeyWord finalExpression] =
    Just $ letExprLetBindFinal (letBindingTextVar var (Left (Prohibit, body))) finalExpression
  mutualReferenceLetExprMultiTokens (MRec : MNonKeyWord var : MEquals : MNonKeyWord body : MComma : rest) =
    letExprLetBind (letBindingTextVar var (Left (Permit, body))) <$> mutualReferenceLetExprMultiTokens rest
  mutualReferenceLetExprMultiTokens (MNonKeyWord var : MEquals : MNonKeyWord body : MComma : rest) =
    letExprLetBind (letBindingTextVar var (Left (Prohibit, body))) <$> mutualReferenceLetExprMultiTokens rest
  mutualReferenceLetExprMultiTokens (MRaw : MNonKeyWord var : MEquals : MNonKeyWord body : MComma : rest) =
    letExprLetBind (letBindingTextVar var (Right body)) <$> mutualReferenceLetExprMultiTokens rest
  mutualReferenceLetExprMultiTokens _ = Nothing
