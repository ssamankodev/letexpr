{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module MyLib.CLIToLetExpr(linearReferenceLetExprParse, mutualReferenceLetExprParse) where

  import Data.Bifunctor
  import Data.Text (Text)
  import Data.Text.Encoding as TE
  import MyLib.LetExpr
  import MyLib.BetaReduce

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

  linearReferenceLetExprParse :: [Text] -> Maybe (LetExpr (Either (RecursionAllowance, Text) Text) Text)
  linearReferenceLetExprParse = linearReferenceLetExprTokens . tokenize

  linearReferenceLetExprTokens :: [Tokens] -> Maybe (LetExpr (Either (RecursionAllowance, Text) Text) Text)
  linearReferenceLetExprTokens tokens = case maybeLinearReferenceLetBindingTypeParse tokens of
    Just (lb, [In , NonKeyWord finalExpression]) -> Just $ letExpr lb finalExpression
    Just (lb, In : following) -> prependLetExpr lb <$> linearReferenceLetExprTokens following
    Just _ -> Nothing
    Nothing -> Nothing

  maybeLinearReferenceLetBindingTypeParse :: [Tokens] -> Maybe (LetBinding (Either (RecursionAllowance, Text) Text), [Tokens])
  maybeLinearReferenceLetBindingTypeParse (Let : rest) =  first (fmap (Left . (Prohibit,))) <$> maybeLinearReferenceLetExprParse rest
  maybeLinearReferenceLetBindingTypeParse (LetRec : rest) =  first (fmap (Left . (Permit,))) <$> maybeLinearReferenceLetExprParse rest
  maybeLinearReferenceLetBindingTypeParse (LetRaw : rest) =  first (fmap Right) <$> maybeLinearReferenceLetExprParse rest
  maybeLinearReferenceLetBindingTypeParse _ = Nothing

  maybeLinearReferenceLetExprParse :: [Tokens] -> Maybe (LetBinding Text, [Tokens])
  maybeLinearReferenceLetExprParse (NonKeyWord var : Equals : NonKeyWord body : rest) = Just (letBindingBS (TE.encodeUtf8 var) body, rest)
  maybeLinearReferenceLetExprParse _ = Nothing

  mutualReferenceLetExprParse :: [Text] -> Maybe (LetExpr (Either (RecursionAllowance, Text) Text) Text)
  mutualReferenceLetExprParse chunks = case multiTokenize chunks of
    (MLet : rest) -> mutualReferenceLetExprMultiTokens rest
    _ -> Nothing

  maybeMutualReferenceLetBindingTypeParse :: [MultiTokens] -> Maybe (LetBinding (Either (RecursionAllowance, Text) Text), [MultiTokens])
  maybeMutualReferenceLetBindingTypeParse (MRec : rest) =  first (fmap (Left . (Permit,))) <$> maybeMutualReferenceLetExprParse rest
  maybeMutualReferenceLetBindingTypeParse (MRaw : rest) =  first (fmap Right) <$> maybeMutualReferenceLetExprParse rest
  maybeMutualReferenceLetBindingTypeParse rest =  first (fmap (Left . (Prohibit,))) <$> maybeMutualReferenceLetExprParse rest

  maybeMutualReferenceLetExprParse :: [MultiTokens] -> Maybe (LetBinding Text, [MultiTokens])
  maybeMutualReferenceLetExprParse (MNonKeyWord var : MEquals : MNonKeyWord body : rest) = Just (letBindingBS (TE.encodeUtf8 var) body, rest)
  maybeMutualReferenceLetExprParse _ = Nothing

  mutualReferenceLetExprMultiTokens :: [MultiTokens] -> Maybe (LetExpr (Either (RecursionAllowance, Text) Text) Text)
  mutualReferenceLetExprMultiTokens tokens = case maybeMutualReferenceLetBindingTypeParse tokens of
    Just (lb, [MIn, MNonKeyWord finalExpression]) -> Just $ letExpr lb finalExpression
    Just (lb, MComma : following) -> prependLetExpr lb <$> mutualReferenceLetExprMultiTokens following
    Just _ -> Nothing
    Nothing -> Nothing
