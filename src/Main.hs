{-# LANGUAGE RankNTypes, FlexibleContexts, CPP #-}

--TODO 種々のアルゴリズムの実装
--     Deltaのデータ構造がよろしくないので改良する
--     PDAにも手を出したい

module Main where

import Automaton
import Data.Set

main :: IO ()
main = do
        print $ dfa3
        putStrLn ""
        print $ removeUnReachable dfa3
        --print $ minimizeDFA dfa3

dfa1 :: Automaton String
dfa1 = Automaton { states      = ["q0","f"]
                 , alphabet    = ['1', '0']
                 , initState   = "q0"
                 , finalStates = ["f"]
                 , delta       = [ ("q0", Symbol '0', "f")
                                 , ("q0", Symbol '1', "q0")
                                 , ("f" , Symbol '0', "f")
                                 , ("f" , Symbol '1', "q0")
                                 ]
                   }

nfa2 :: Automaton String
nfa2 = Automaton { states      = ["q0","f"]
                 , alphabet    = ['1', '0']
                 , initState   = "q0"
                 , finalStates = ["f"]
                 , delta       = [ ("q0", Symbol '0', "f")
                                 , ("q0", Symbol '1', "q0")
                                 , ("f" , Symbol '0', "f")
                                 , ("f" , Null      , "q0")
                                 ]
                   }

dfa3 :: Automaton Char
dfa3 = Automaton { states      = ['a'..'h']
                 , alphabet    = ['1', '0']
                 , initState   = 'a'
                 , finalStates = ['c']
                 , delta       = [ ('a', Symbol '0', 'b')
                                 , ('a', Symbol '1', 'f')
                                 , ('b', Symbol '0', 'g')
                                 , ('b', Symbol '1', 'c')
                                 , ('c', Symbol '0', 'a')
                                 , ('c', Symbol '1', 'c')
                                 , ('d', Symbol '0', 'c')
                                 , ('d', Symbol '1', 'g')
                                 , ('e', Symbol '0', 'h')
                                 , ('e', Symbol '1', 'f')
                                 , ('f', Symbol '0', 'c')
                                 , ('f', Symbol '1', 'g')
                                 , ('g', Symbol '0', 'g')
                                 , ('g', Symbol '1', 'e')
                                 , ('h', Symbol '0', 'g')
                                 , ('h', Symbol '1', 'c')
                                 ]
                   }

printEither :: (Show a) => Either String a -> IO ()
printEither = either putStrLn print

