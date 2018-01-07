{-# Language StandaloneDeriving #-}

import NNFTableau
import Data.Map (Map)
import qualified Data.Map as M
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (emptyDef)
import Text.Parsec.Expr
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec

lexer = P.makeTokenParser emptyDef
reservedOp = P.reservedOp lexer
parens = P.parens lexer
lexeme = P.lexeme lexer

deriving instance Show Formula

instance Show Decision where
  show Closed = "Closed"
  show (Open _) = "Open"

instance Show Tree where
  show x = show (elements x)

instance Show Tableau where
  show ClosedTableau = "Closed"
  show (OpenTableau _) = "Open"
  show (AndRule gamma _ _ t) = "AndRule " ++ show gamma ++ " (" ++ show t ++ ")"
  show (OrRule gamma1 gamma2 _ _ _ t1 t2) = "OrRule " ++ show gamma1 ++ " (" ++ show t1 ++ ") " ++ show gamma2 ++ " (" ++ show t2 ++ ")"

expr = buildExpressionParser table (lexeme term)

term = parens expr
   <|> (Var <$> many1 letter)

table = [[Prefix (reservedOp "~" >> return neg)],
         [binary "/\\" PAnd AssocRight],
         [binary "\\/" POr AssocRight]]

binary name fun assoc = Infix (reservedOp name >> return fun) assoc

data PFormula a
   = Var a
   | Neg a
   | PAnd (PFormula a) (PFormula a)
   | POr (PFormula a) (PFormula a)
  deriving Show

neg (Var s) = Neg s

getVars :: PFormula String -> Integer -> Map String Integer -> (Map String Integer, Integer)
getVars (Var s) n m = case M.lookup s m of
  Nothing -> (M.insert s n m, n+1)
  Just _ -> (m,n)
getVars (Neg s) n m = case M.lookup s m of
  Nothing -> (M.insert s n m, n+1)
  Just _ -> (m,n)
getVars (PAnd x y) n m = let (m', n') = getVars x n m in getVars y n' m'
getVars (POr x y) n m = let (m', n') = getVars x n m in getVars y n' m'

convertToFormula :: PFormula String -> Map String Integer -> Formula
convertToFormula (Var v) m = PosVar (m M.! v)
convertToFormula (Neg v) m = NegVar (m M.! v)
convertToFormula (PAnd x y) m = And (convertToFormula x m) (convertToFormula y m)
convertToFormula (POr x y) m = Or (convertToFormula x m) (convertToFormula y m)

main = do
  s <- getLine
  let (Right f) = parse expr "" s
  let (m,_) = getVars f 0 M.empty
  case tableau_list [convertToFormula f m] of 
    Nothing -> putStrLn "Closed"
    Just v -> do
      putStrLn "Open"
      mapM_ putStrLn [s ++ " |-> " ++ show (v k) | (s,k) <- M.assocs m]
