{-# LANGUAGE FlexibleInstances
           , UndecidableInstances
           , IncoherentInstances
           #-}

module Automaton where

--{{{import
import Data.List (foldl', sort, nub, nubBy)
import qualified Data.Map.Strict as Map
import Data.Set (Set, fromList, member, union, empty, singleton)
import qualified Data.Set as Set
import Data.Union.ST   as UST
import Control.Monad.ST
import Control.Monad.State
import Control.Applicative (Applicative(..), Alternative(..), (<$>) )
--}}}

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
type Delta a  = [(a, Symbol, a)] -- Map a [(Symbol, a)] にするのがよい

data Set' a = Set' [a]
instance (Eq a, Ord a) => Eq (Set' a) where
        (Set' xs) == (Set' ys) = length xs == length ys && sort xs == sort ys
instance (Eq a, Ord a) =>  Ord (Set' a) where
        (Set' xs) `compare` (Set' ys) = sort xs `compare` sort ys
instance (Ord a, Show a) => Show (Set' a) where
        show (Set' xs) = "{" ++ f (sort xs) ++ "}"
            where f [] = ""
                  f [x] = show x
                  f (x:xs) = show x ++ ", " ++ f xs
instance Functor Set' where
        fmap f (Set' xs) = Set' (map f xs)
mapSet' :: ([a] -> [b]) -> Set' a -> Set' b
mapSet' f (Set' as) = Set' (f as)
-- }}}

--{{{isDFA
isDFA :: (Eq a, Ord a, Show a) => Automaton a -> Either String Bool
isDFA (Automaton _Q _Σ δ q0 _F)
    | null _Q                    = Left "error: Q is empty"
    | q0 `notElem` _Q            = Left $ "error: q0 not in Q: " ++ show q0 ++ " : " ++ show _Q
    | not (_F `isSubsetOf` _Q)   = Left "error: F \\not \\in Q"
    | not (δ `isFuncOn` (_Q,_Σ)) = Right False --NFA
    | otherwise                  = Right True  --DFA
    where
        isSubsetOf :: (Eq a) => [a] -> [a] -> Bool
        isSubsetOf a b = all (`elem` b) a
        isFuncOn :: (Eq a, Ord a) => Delta a -> ([a] , Alphabet) -> Bool
        isFuncOn δ (qS, alphabet) = flip all qS $ \q->        --forall q \in qS
                                    flip all alphabet $ \a->  --forall a \in alphabet
                                    length (filter (\q'->(q, Symbol a,q') `elem` δ) qS) == 1
-- }}}

-- computation{{{
str2word :: String -> Word'
str2word = map Symbol

transitDFA :: (Eq a, Show a) => Delta a -> a -> Symbol -> a
transitDFA δ q Null = q --XXX不要では
transitDFA δ q x = let l = [ q2 | (q1, x', q2) <- δ, q1==q && x==x']
                   in case l of
                          []        -> error $ "transitDFA: empty list:\n" ++
                                               "  symbol: " ++ show x ++ "\n" ++
                                               "  state: "  ++ show q ++ "\n" ++
                                               "  delta: "  ++ show δ
                          [x]       -> x
                          otherwise -> error "transitDFA: なんでやねん"
transitsDFA :: (Eq a, Show a) => Delta a -> a -> Word' -> a
transitsDFA δ = foldl' (transitDFA δ)

transitNFA :: (Eq a, Ord a, Show a) => Delta a -> [a] -> Symbol -> [a]
transitNFA δ qs x = concatMap (\q -> [ q2 | (q1, x', q2) <- δ, q1 == q && x == x']) (nullTransit δ qs)
transitsNFA :: (Eq a, Ord a, Show a) => Delta a -> [a] -> Word' -> [a]
transitsNFA δ qs x = nullTransit δ $ foldl' (transitNFA δ) qs x

nullTransit :: (Eq a, Ord a, Show a) => Delta a -> [a] -> [a]
nullTransit δ qs = let newqs = concatMap (\q -> [ q2 | (q1, Null, q2) <- δ, q1 == q, q2 `notElem` qs]) qs
                   in if null newqs then qs
                                    else nullTransit δ $ newqs ++ qs -- δいる理由は?

computation :: (Eq a, Ord a, Show a) => String -> Automaton a -> Either String [a]
computation x m@(Automaton qS alphabet δ q0 fS) =
        if (`notElem` alphabet) `any` x
            then Left $ "error: \"" ++ x ++ "\" is not a word on \"" ++ alphabet ++ "\""
            else case isDFA m of
                   Right True  -> let w = str2word x
                                  in Right [transitsDFA δ q0 w]
                   Right False -> let w = str2word x
                                  in Right $ transitsNFA δ [q0] w
                   Left err -> Left err

isAcceptedBy :: (Eq a, Ord a, Show a) => String -> Automaton a -> Either String Bool
isAcceptedBy x m@(Automaton qS alphabet δ q0 fS) =
        case computation x m of
            Right qs -> if (`notElem` fS) `all` qs then Right False else Right True
            Left err -> Left err

sizeOf :: Automaton a -> Int
sizeOf (Automaton qS _ _ _ _) = length qS
-- }}}

--algorithm-- {{{
powersetConstruction :: (Eq a, Ord a, Show a) => Automaton a -> Automaton (Set a)-- {{{
--make sure that the automaton is not DFA
powersetConstruction m@(Automaton qS alphabet δ q0 fS) =
            Automaton newqS alphabet newδ newq0 newfS
        where
            newq0 = fromList $ nullTransit δ [q0]
            newqS = map fromList pqS
            newfS = map fromList $ filter (\qs -> (`elem` qs) `any` fS) pqS
            newδ  = let f qs x = nullTransit δ $
                                 flip filter qS $ \q -> --take q \in qS s.t.
                                 flip any qs $ \p ->    --exists p \in newq s.t.
                                 (p, x, q) `elem` δ     --(p, x, q) \in δ
                        chokuseki = [(qs, Symbol a)| qs <- pqS, a <- alphabet]
                    in map (\(qs, x) -> (fromList qs, x, fromList (f qs x))) chokuseki
            pqS = powerSet qS
            powerSet []     = [[]]
            powerSet (x:xs) = let pxs = powerSet xs in map (x:) pxs ++ pxs
-- }}}

minimizeDFA :: (Eq a, Ord a, Show a) => Automaton a -> Automaton (Set' a)-- {{{
minimizeDFA m = let m' = removeUnReachable m
                    eqvSet = getEqvStates m'
                in groopState m' eqvSet

removeUnReachable :: (Eq a, Ord a, Show a) => Automaton a -> Automaton a
removeUnReachable m@(Automaton qS alphabet δ q0 fS) =
        let reachableFrom qs = let l = nub $ concatMap (\q -> [ q2 | (q1, _, q2) <- δ, q1 == q, q2 `notElem` qs]) qs
                               in if null l then qs else reachableFrom $ l ++ qs
            newqS = sort $ reachableFrom [q0]
            newfS = filter (`elem`  newqS) fS
            newδ  = filter (\(p,x,q) -> (p `elem` newqS) && (q `elem` newqS)) δ
        in Automaton newqS alphabet newδ q0 newfS

getEqvStates :: (Eq a, Ord a, Show a) => Automaton a -> Set (a,a)
getEqvStates m@(Automaton qS alphabet δ q0 fS) =
            let complementF = filter (`notElem` fS) qS
                marked    = Set.fromList [(p,q) | p <- fS, q <- complementF, p<q]
                unMarked  = Set.fromList $ [(p,q) | p <- fS, q <- fS, p<q] ++ [(p,q) | p <- complementF, q <- complementF, p<q]
                (_, unMarked') = run (marked, unMarked)
            in unMarked'
        where
            run (marked, unMarked) =
                let l = flip Set.filter unMarked $ \(p,q) ->
                        flip any alphabet $ \a ->
                        let pa = transitDFA δ p (Symbol a)
                            qa = transitDFA δ q (Symbol a)
                        in (pa, qa) `Set.member` marked || (qa, pa) `Set.member` marked
                in if Set.null l
                       then (marked, unMarked)
                       else run (marked `Set.union` l, unMarked `Set.difference` l)

groopState :: (Eq a, Ord a, Show a) => Automaton a -> Set (a,a) -> Automaton (Set' a)--Automaton (Set' a)
groopState m@(Automaton qS alphabet δ q0 fS) eqvSet = runST $ do
        --initialize
        ufTree <- UST.new (sizeOf m) [q0]
        let dic     = Map.fromList $ zip qS ([0..]::[Int])
            keyOf q = dic Map.! q
            mapAnnotate q n b = b >> UST.annotate ufTree n [q] >> return ()
        Map.foldrWithKey' mapAnnotate (return ()) dic
        --make eqv groop
        let union (p,q) = UST.merge ufTree (\p q->(p++q,())) (keyOf p) (keyOf q)
        forM_ eqvSet union
        --make Automaton
        let φ q = snd <$> UST.lookup ufTree (keyOf q)
        newq0 <- Set' <$> φ q0
        newqS <- map Set' . nub <$> mapM φ qS
        newfS <- map Set' . filter (\qs -> (`elem` fS) `any` qs) <$> mapM φ qS
        newδ  <- nub <$> mapM (\(p,x,q)-> do {p' <- φ p; q' <- φ q ; return (Set' p', x, Set' q')}) δ
        return $ Automaton newqS alphabet newδ newq0 newfS
-- }}}

-- }}}

