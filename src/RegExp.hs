
module RegExp where

import Automaton
import Control.Monad.State
import Text.Parsec hiding (Empty, State)
import Text.Parsec.String

--なんかバグあるっぽいので全面的に書き直します

--正規表現 -> NFA-- {{{
data RegExp = Empty
            | Symbol' Char
            | Kleene  RegExp
            | Product [RegExp]
            | Union   RegExp RegExp
            deriving (Show, Eq)

regExpParse :: Alphabet -> String -> Either ParseError RegExp
regExpParse alphabet = parse (expr <* eof) ""
    where
        expr   = chainr1 term (char '+' >> return Union)
        term   = Product <$> many factor
        factor = try (Kleene <$> simple <* char '*') <|> simple
        simple = try (Symbol' <$> oneOf alphabet)
                 <|> (between (char '(') (char ')') term)
                 <|> (string "\\0" >> return Empty)

regExp2NFA :: Alphabet -> RegExp -> Automaton Int
regExp2NFA _Σ regExp = evalState (regExp2NFA_ _Σ regExp) 0

regExp2NFA_ :: Alphabet -> RegExp -> State Int (Automaton Int)
regExp2NFA_ _Σ regExp = case regExp of
      Empty -> do
          (q0,f) <- newStates
          return $ Automaton [q0,f] _Σ [] q0 [f]
      Symbol' a -> do
          (q0,f) <- newStates
          return $ Automaton [q0,f] _Σ [(q0, Symbol a, f)] q0 [f]
      Kleene regExp' -> do
          (q0,f) <- newStates
          Automaton _Q' _ δ' q0' [f'] <- regExp2NFA_ _Σ regExp'
          let _Q = _Q' ++ [q0,f]
              δ  = δ' ++ [(q0,Null,q0'), (q0,Null,f), (f',Null,q0'), (f',Null,f)]
          return $ Automaton _Q _Σ δ q0 [f]
      Product [] -> do --来ることあるかな？
          q0 <- newState
          return $ Automaton [q0] _Σ [] q0 [q0]
      Product [r] -> regExp2NFA_ _Σ r
      Product (r:rs) -> do
          Automaton _Q1 _ δ1 q1 [f1] <- regExp2NFA_ _Σ r
          Automaton _Q2 _ δ2 q2 [f2] <- regExp2NFA_ _Σ (Product rs)
          let _Q = _Q1 ++ _Q2
              δ  = δ1 ++ δ2 ++ [(f1,Null,q2)]
          return $ Automaton _Q _Σ δ q1 [f2]
      Union regExp1 regExp2 -> do
          (q0,f) <- newStates
          Automaton _Q1 _ δ1 q1 [f1] <- regExp2NFA_ _Σ regExp1
          Automaton _Q2 _ δ2 q2 [f2] <- regExp2NFA_ _Σ regExp2
          let _Q = _Q1 ++ _Q2 ++ [q0,f]
              δ  = δ1 ++ δ2 ++ [(q0,Null,q1), (q0,Null,q2), (f1,Null,f), (f2,Null,f)]
          return $ Automaton _Q _Σ δ q0 [f]

      where
        newState = get <* modify (+1)
        newStates = (,) <$> newState <*> newState

-- }}}
