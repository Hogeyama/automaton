
module Automaton where

--{{{import
import Data.List (foldl', sort, nub, nubBy)
import Data.Map.Strict (Map)
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

instance (Show a) => Show (Automaton a) where
        show (Automaton qS alphabet δ q0 fS) =
            "Q:  " ++ show qS ++ "\n" ++
            "Σ:  " ++ show alphabet ++ "\n" ++
            "δ:  " ++ show δ  ++ "\n" ++
            "q0: " ++ show q0 ++ "\n" ++
            "F:  " ++ show fS
type Alphabet = String
type Word'    = [Symbol]
data Symbol   = Symbol Char | Null
                deriving (Show,Eq)
type Delta a  = Map.Map a [(Symbol, a)]

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

partialApp :: (Ord a) => Delta a -> a -> [(Symbol, a)]
partialApp δ q = Map.findWithDefault [] q δ
-- }}}

--list <--> Delta-- {{{
--O(QΣlogQ)
listToDelta :: (Ord a) => [a] -> [(a, Symbol, a)] -> Delta a
listToDelta qS l = let δ0 = Map.fromList $ map (\q -> (q,[])) qS
                       f (p, x, q) δ = Map.update (\δp -> Just ((x,q):δp)) p δ
                   in foldr f δ0 l

--O(QΣ)
listFromDelta :: Delta a -> [(a, Symbol, a)]
listFromDelta m = Map.foldrWithKey' f [] m
        where f p δp l = l ++ map (\(x,q) -> (p,x,q)) δp
-- }}}

--{{{isDFA
isDFA :: (Eq a, Ord a) => Automaton a -> Either String Bool
isDFA (Automaton _Q _Σ δ q0 _F)
    | null _Q                    = Left "error: Q is empty"
    | q0 `notElem` _Q            = Left $ "error: q0 not in Q:"
    | not (_F `isSubsetOf` _Q)   = Left "error: F \\not \\in Q"
    | not (δ `isFuncOn` (_Q,_Σ)) = Right False --NFA
    | otherwise                  = Right True  --DFA
    where
        isSubsetOf :: (Eq a) => [a] -> [a] -> Bool
        isSubsetOf a b = all (`elem` b) a
        isFuncOn :: (Eq a, Ord a) => Delta a -> ([a] , Alphabet) -> Bool
        isFuncOn δ (qS, alphabet) = flip all qS $ \q->        --forall q \in qS
                                    flip all alphabet $ \a->  --forall a \in alphabet
                                    length [ () | (Symbol b, _) <- δ `partialApp` q, a == b] == 1
-- }}}

-- computation{{{
str2word :: String -> Word'
str2word = map Symbol

transitDFA :: (Eq a, Ord a) => Delta a -> a -> Symbol -> a
transitDFA δ q Null = q --XXX不要では
transitDFA δ q x = let l = [ q2 | (x', q2) <- δ `partialApp` q, x==x']
                   in case l of [x]       -> x
                                otherwise -> error "transitDFA: なんでやねん"
transitsDFA :: (Eq a, Ord a) => Delta a -> a -> Word' -> a
transitsDFA δ = foldl' (transitDFA δ)

transitNFA :: (Eq a, Ord a) => Delta a -> [a] -> Symbol -> [a]
transitNFA δ qs x = concatMap (\q -> [ q' | (x', q') <- δ `partialApp` q, x == x']) (nullTransit δ qs)
transitsNFA :: (Eq a, Ord a) => Delta a -> [a] -> Word' -> [a]
transitsNFA δ qs x = nullTransit δ $ foldl' (transitNFA δ) qs x

nullTransit :: (Eq a, Ord a) => Delta a -> [a] -> [a]
nullTransit δ qs = let newqs = concatMap (\q -> [ q' | (Null, q') <- δ `partialApp` q, q' `notElem` qs]) qs
                   in if null newqs then qs
                                    else nullTransit δ $ newqs ++ qs -- δいる理由は?

computation :: (Eq a, Ord a) => String -> Automaton a -> Either String [a]
computation x m@(Automaton qS alphabet δ q0 fS) =
        if (`notElem` alphabet) `any` x
            then Left $ "error: \"" ++ x ++ "\" is not a word on \"" ++ alphabet ++ "\""
            else case isDFA m of
                   Right True  -> let w = str2word x
                                  in Right [transitsDFA δ q0 w]
                   Right False -> let w = str2word x
                                  in Right $ transitsNFA δ [q0] w
                   Left err -> Left err

isAcceptedBy :: (Eq a, Ord a) => String -> Automaton a -> Either String Bool
isAcceptedBy x m@(Automaton qS alphabet δ q0 fS) =
        case computation x m of
            Right qs -> if (`notElem` fS) `all` qs then Right False else Right True
            Left err -> Left err

sizeOf :: Automaton a -> Int
sizeOf (Automaton qS _ _ _ _) = length qS
-- }}}

--algorithms-- {{{
powersetConstruction :: (Eq a, Ord a) => Automaton a -> Automaton (Set' a)-- {{{
--make sure that the automaton is not DFA
powersetConstruction m@(Automaton qS alphabet δ q0 fS) =
            Automaton newqS alphabet newδ newq0 newfS
        where
            newq0 = Set' $ nullTransit δ [q0]
            newqS = map Set' pqS
            newfS = map Set' $ filter (\qs -> (`elem` qs) `any` fS) pqS
            newδ  = let f qs x = nullTransit δ $
                                 flip filter qS $ \q ->           --take q \in qS s.t.
                                 flip any qs $ \p ->              --exists p \in qs s.t.
                                 (x, q) `elem` (δ `partialApp` p) --(p, x, q) \in δ (= (x,p) \in δ(q))
                        chokuseki = [(qs, Symbol a)| qs <- pqS, a <- alphabet]
                    in listToDelta newqS $ map (\(qs, x) -> (Set' qs, x, Set' (f qs x))) chokuseki
            pqS = powerSet qS
            powerSet []     = [[]]
            powerSet (x:xs) = let pxs = powerSet xs in map (x:) pxs ++ pxs
-- }}}

minimizeDFA :: (Eq a, Ord a) => Automaton a -> Automaton (Set' a)-- {{{
minimizeDFA m = let m' = removeUnReachable m
                    eqvSet = getEqvStates m'
                in groopState m' eqvSet

removeUnReachable :: (Eq a, Ord a) => Automaton a -> Automaton a
removeUnReachable m@(Automaton qS alphabet δ q0 fS) =
        let reachableFrom qs = let l = nub $ concatMap (\q -> [ q' | (_, q') <- δ `partialApp` q, q' `notElem` qs]) qs
                               in if null l then qs else reachableFrom $ l ++ qs
            newqS = sort $ reachableFrom [q0]
            newfS = filter (`elem`  newqS) fS
            newδ  = Map.filterWithKey (\q _ -> q `elem` newqS) $
                    Map.map (\l -> [(x,q)| (x,q) <- l, q `elem` newqS]) δ
        in Automaton newqS alphabet newδ q0 newfS

getEqvStates :: (Eq a, Ord a) => Automaton a -> Set (a,a)
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

groopState :: (Eq a, Ord a) => Automaton a -> Set (a,a) -> Automaton (Set' a)--Automaton (Set' a)
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
        newδ  <- (listToDelta newqS . nub) <$> mapM (\(p,x,q)-> do {p' <- φ p; q' <- φ q ; return (Set' p', x, Set' q')}) (listFromDelta δ)
        return $ Automaton newqS alphabet newδ newq0 newfS
-- }}}

--completment {{{
commplementDFA :: (Eq a, Ord a) => Automaton a -> Automaton a
commplementDFA m@(Automaton qS alphabet δ q0 fS) =
        let newfS = filter (`notElem` fS) qS
        in Automaton qS alphabet δ q0 newfS

completmentNFA :: (Eq a, Ord a) => Automaton a -> Automaton (Set' a)
completmentNFA = commplementDFA . powersetConstruction
-- }}}

acceptNoWord :: (Eq a, Ord a) => Automaton a -> Bool-- {{{効率悪い
acceptNoWord m = let Automaton _ _ _ _ fS = removeUnReachable m
                 in null fS
-- }}}

product :: (Eq a, Ord a, Eq b, Ord b) => Automaton a -> Automaton b -> Automaton (a,b) --{{{ O(QaQbΣΣ)
product m1@(Automaton qS1 alphabet δ1 q01 fS1) m2@(Automaton qS2 alphabet' δ2 q02 fS2) =
    if sort alphabet /= sort alphabet'
      then error "product: 2 alphabets must be the same."
      else let newqS = [(q1, q2)| q1 <- qS1, q2 <- qS2]
               newfS = [(q1, q2)| q1 <- fS1, q2 <- fS2]
               newq0 = (q01, q02)
               newδ  = let f (q1,q2) δ = let l1 = δ1 `partialApp` q1
                                             l2 = δ2 `partialApp` q2
                                             l  = concatMap (\(x,p2) -> [(x,(p1,p2))| (x',p1)<-l1, x==x']) l2
                                         in Map.insert (q1,q2) l δ
                       in foldr f Map.empty newqS
           in Automaton newqS alphabet newδ newq0 newfS
--}}}

-- }}}
