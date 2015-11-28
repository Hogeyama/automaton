{-# LANGUAGE FlexibleInstances
           , UndecidableInstances
           , IncoherentInstances
           #-}

module Automaton where

--{{{import
import Data.List (foldl', sort, nub, nubBy)
import Control.Monad.State
import Control.Applicative (Applicative(..), Alternative(..), (<$>) )
import Text.Parsec hiding (Empty, (<|>), many, State, Error)
--}}}

--Eq'クラス-- {{{
--リストの相当性を集合としての相当性で考える
--ただしStringはCharの集合とは考えない
class (Eq a) => Eq' a where
    (===) :: a -> a -> Bool
instance (Eq a) => Eq' a where
    x === y = x == y
instance (Ord a, Eq' a) => Eq' [a] where
    xs === ys = (length xs == length ys) && and (zipWith (===) (sort xs) (sort ys))
instance Eq' String where
    x === y = x == y

elem_ :: (Eq' a) => a -> [a] -> Bool
elem_ = any . (===)

notElem_ :: (Eq' a) => a -> [a] -> Bool
notElem_ x = not . elem_ x

isSubsetOf_ :: (Eq' a) => [a] -> [a] -> Bool
isSubsetOf_ a b = all (`elem_` b) a

nub_ :: (Eq' a) => [a] -> [a]
nub_ = nubBy (===)
-- }}}

--data宣言-- {{{
data Automaton a = Automaton { states :: [a]
                           , alphabet :: Alphabet
                           , delta :: Delta a
                           , initState :: a
                           , finalStates :: [a]
                           }

instance (Eq a, Show a) => Show (Automaton a) where
        show (Automaton qS alphabet δ q0 fS) =
            "Q:  " ++ show qS ++ "\n" ++
            "Σ:  " ++ show alphabet ++ "\n" ++
            "δ:  " ++ show δ  ++ "\n" ++
            "q0: " ++ show q0 ++ "\n" ++
            "F:  " ++ show fS
type Alphabet = String
type Word'    = [Symbol]
data Symbol   = Symbol Char | Null --ε遷移を考えるとき必要
                deriving (Show,Eq)
type Delta a  = [(a, Symbol, a)]

-- }}}

--{{{isDFA
isDFA :: (Eq' a, Ord a, Show a) => Automaton a -> Either String Bool
isDFA (Automaton _Q _Σ δ q0 _F)
    | null _Q                    = Left "error: Q is empty"
    | q0 `notElem_` _Q            = Left $ "error: q0 not in Q: " ++ show q0 ++ " : " ++ show _Q
    | not (_F `isSubsetOf_` _Q)   = Left "error: F \\not \\in Q"
    | not (δ `isFuncOn` (_Q,_Σ)) = Right False --NFA
    | otherwise                  = Right True  --DFA
    where
        isFuncOn :: (Eq' a, Ord a) => Delta a -> ([a] , Alphabet) -> Bool
        isFuncOn δ (qS, alphabet) = flip all qS $ \q->        --forall q \in qS
                                    flip all alphabet $ \a->  --forall a \in alphabet
                                    length (filter (\q'->(q, Symbol a,q') `elem` δ) qS) == 1
-- }}}

-- computation{{{
str2word :: String -> Word'
str2word = map Symbol

transitDFA :: (Eq' a, Show a) => Delta a -> a -> Symbol -> a
transitDFA δ q Null = q
transitDFA δ q x = let l = [ q2 | (q1, x', q2) <- δ, q1===q && x==x']
                   in case l of
                          []        -> error $ "transitDFA: empty list:\n" ++
                                               "  symbol: " ++ show x ++ "\n" ++
                                               "  state: "  ++ show q ++ "\n" ++
                                               "  delta: "  ++ show δ
                          [x]       -> x
                          otherwise -> error "transitDFA: なんでやねん"
transitsDFA :: (Eq' a, Show a) => Delta a -> a -> Word' -> a
transitsDFA δ = foldl' (transitDFA δ)

transitNFA :: (Eq' a, Ord a, Show a) => Delta a -> [a] -> Symbol -> [a]
transitNFA δ qs x = concatMap (\q -> [ q2 | (q1, x', q2) <- δ, q1 === q && x == x']) (nullTransit δ qs)
transitsNFA :: (Eq' a, Ord a, Show a) => Delta a -> [a] -> Word' -> [a]
transitsNFA δ qs x = nullTransit δ $ foldl' (transitNFA δ) qs x

nullTransit :: (Eq' a, Ord a, Show a) => Delta a -> [a] -> [a]
nullTransit δ qs = let newqs = concatMap (\q -> [ q2 | (q1, Null, q2) <- δ, q1 === q, q2 `notElem` qs]) qs
                   in if null newqs then qs
                                    else nullTransit δ $ qs ++ newqs

computation :: (Eq' a, Ord a, Show a) => String -> Automaton a -> Either String [a]
computation x m@(Automaton qS alphabet δ q0 fS) =
        if (`notElem` alphabet) `any` x
            then Left $ "error: \"" ++ x ++ "\" is not a word on \"" ++ alphabet ++ "\""
            else case isDFA m of
                   Right True  -> let w = str2word x
                                  in Right [transitsDFA δ q0 w]
                   Right False -> let w = str2word x
                                  in Right $ transitsNFA δ [q0] w
                   Left err -> Left err

isAcceptedBy :: (Eq' a, Ord a, Show a) => String -> Automaton a -> Either String Bool
isAcceptedBy x m@(Automaton qS alphabet δ q0 fS) =
        case computation x m of
            Right qs  -> if (`notElem_` fS) `all` qs then Right False else Right True
            Left err -> Left err

sizeOf :: Automaton a -> Int
sizeOf (Automaton qS _ _ _ _) = length qS
-- }}}

--algorithm-- {{{
--make sure that the automaton is not DFA
powersetConstruction :: (Eq a, Ord a, Show a) => Automaton a -> Automaton [a]
powersetConstruction m@(Automaton qS alphabet δ q0 fS) =
            Automaton newqS alphabet newδ newq0 newfS
        where
            newq0 = nullTransit δ [q0]
            newqS = powerSet qS
            newfS = filter (\newq -> (`elem_` newq) `any` fS) newqS
            newδ  = let f newq x = nullTransit δ $
                                   flip filter qS $ \q -> --take q \in qS s.t.
                                   flip any newq $ \p ->  --exists p \in newq s.t.
                                   (p, x, q) `elem` δ     --(p, x, q) \in δ
                        chokuseki = [(newq, Symbol a)| newq <- newqS, a <- alphabet]
                    in map (\(newq, x) -> (newq, x, f newq x)) chokuseki
            powerSet []     = [[]]
            powerSet (x:xs) = let pxs = powerSet xs
                              in map (x:) pxs ++ pxs

minimizeDFA :: Automaton a -> Automaton [a]
minimizeDFA = undefined
-- }}}

